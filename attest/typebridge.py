"""TypeDB's type system <-> Lean, kept in sync. Core: no domain in it.

Every path, namespace and module list is
supplied by the caller, so a domain's Lean package can live anywhere and a
repository can hold several.


  parse(type_schema)        live TypeDB schema text -> type model
  render(store, ns)         type model -> the Lean module of types (+ schema hash)
  generate(store, path, ns) render, and write it to `path`
  lean_literal(model, T, r) a TypeDB row -> a Lean value of the generated type T
  lean_str(s)               any string -> an exact Lean string literal
  publish(store, ...)       Lean modules -> TypeDB `artifact` entities (by hash)
  check_sync(store, ...)    refuse to verify unless the Lean types on disk are
                            exactly what the live schema renders to, and every
                            source in use is published
  materialize(store, ids)   rebuild a Lean workspace from artifacts in TypeDB

Mapping (TypeDB -> Lean):
  attribute with @values      -> inductive (one constructor per value)
  entity / relation type      -> structure (roles + owned attributes as fields)
  relates r @card(1..1)       -> field r : String   (the role player's key)
  relates r (any other card)  -> field r : List String
  owns a @key / @card(1..1)   -> required field
  owns a (default / 0..1)     -> Option field
  value integer               -> Int
  value string / datetime     -> String (datetimes as ISO-8601)

The bridge does not trust its own translation. Every generated proof stands on
these types and literals, so anything it cannot represent EXACTLY is refused
(`UnsupportedSchema`), never approximated: an unknown statement, clause or
annotation; a value type with no Lean mapping; a multi-valued attribute; two
TypeDB names that would become one Lean name. The same goes for data: a row
whose keys or value shapes do not match the generated type is refused.
"""
import hashlib, json, os, re, shutil, subprocess, tempfile
from dataclasses import dataclass, field

#: artifact kinds that are Lean modules and belong in a rebuilt workspace
LEAN_KINDS = frozenset({"schema-types", "rule-library", "theorems"})

#: Lean 4 keywords and command words that cannot be a field or constructor
#: name. Tested one by one against Lean as structure fields.
LEAN_KEYWORDS = {
    "end", "def", "theorem", "lemma", "fun", "match", "with", "if", "then",
    "else", "do", "let", "in", "where", "structure", "inductive", "class",
    "instance", "open", "namespace", "import", "by", "at", "from", "unsafe",
    "partial", "private", "protected", "variable", "section", "have", "show",
    "Type", "Prop", "Sort", "deriving", "extends", "mutual", "abbrev", "axiom",
    "sorry", "calc", "example", "universe", "nomatch", "opaque", "notation",
    "suffices", "forall", "exists", "noncomputable", "local", "scoped",
    "export", "nofun", "omit", "include", "elab", "syntax", "macro", "for",
    "unless", "mut", "break", "continue", "catch", "finally", "return", "try",
    "attribute", "builtin_initialize", "initialize", "set_option", "macro_rules",
    "elab_rules", "infix", "infixl", "infixr", "prefix", "postfix", "this",
    "using", "hiding", "renaming", "termination_by", "decreasing_by", "fun",
    "λ", "Π", "Σ", "∀", "∃", "deriving", "theorem", "true", "false",
}

#: names Lean generates on every structure and inductive (or that a generated
#: name would shadow); a field or constructor with one of these names clashes
RESERVED_MEMBERS = {
    "mk", "rec", "recOn", "casesOn", "noConfusion", "noConfusionType",
    "brecOn", "binductionOn", "below", "ibelow", "toCtorIdx", "ctorIdx",
    "sizeOf", "inj", "injEq", "induct", "default",
}

#: type names a generated `structure`/`inductive` must not take: inside the
#: generated namespace it would SHADOW the prelude type, and a field typed
#: `String` would silently mean the domain's type instead
RESERVED_TYPES = {
    "String", "Int", "Nat", "List", "Option", "Bool", "Prop", "Type", "Sort",
    "Char", "Unit", "PUnit", "Decidable", "DecidableEq", "Eq", "Ne", "And",
    "Or", "Not", "True", "False", "Exists", "Iff", "Fin", "Array", "Float",
    "IO", "Id", "Prod", "Sum", "Subtype", "Sigma", "Repr", "BEq", "Hashable",
    "Inhabited", "UInt8", "UInt16", "UInt32", "UInt64", "Snapshot",
}

#: TypeDB value types with an exact Lean representation
VALUE_TYPES = {"string": "String", "integer": "Int", "datetime": "String"}

_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_QUOTED = r'"(?:\\.|[^"\\])*"'


class UnsupportedSchema(Exception):
    """The schema uses something the bridge cannot represent exactly."""


def sha(s):
    return hashlib.sha256(s.encode() if isinstance(s, str) else s).hexdigest()


def pascal(n):
    out = "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_]", n))
    if not _IDENT.match(out) or out in LEAN_KEYWORDS or out in RESERVED_TYPES:
        raise UnsupportedSchema(
            f"type name {n!r} becomes {out!r} in Lean, which is not a usable "
            f"type name there (a keyword, a prelude type it would shadow, or "
            f"not an identifier)")
    return out


def camel(n):
    parts = re.split(r"[-_]", n)
    p = "".join(x[:1].upper() + x[1:] for x in parts)
    out = p[:1].lower() + p[1:]
    if out[:1].isdigit():
        out = "_" + out
    if not _IDENT.match(out):
        raise UnsupportedSchema(f"name {n!r} cannot be a Lean field name")
    return out + "_" if out in LEAN_KEYWORDS or out in RESERVED_MEMBERS else out


def ctor(v):
    if not isinstance(v, str) or v == "":
        raise UnsupportedSchema(f"enum value {v!r} cannot be a Lean constructor")
    c = re.sub(r"[^A-Za-z0-9_]", "_", v)
    if c[:1].isdigit():
        c = "_" + c            # `1st_` is still not an identifier; `_1st` is
    return c + "_" if c in LEAN_KEYWORDS or c in RESERVED_MEMBERS else c


# ------------------------------------------------------------ exact literals
def lean_str(s):
    """An exact Lean 4 string literal for `s`.

    `json.dumps` is NOT one: it writes characters outside the Basic
    Multilingual Plane as UTF-16 surrogate pairs (`"\\ud83d\\ude00"`), Lean
    reads each half as U+0000, and two different emoji become the same Lean
    string — the kernel then proves distinct TypeDB values equal. Lean source
    is UTF-8, so printable characters are written as themselves; only the
    quote, the backslash and control characters are escaped. A string that
    cannot be UTF-8 (a lone surrogate) is refused, not mangled.
    """
    if not isinstance(s, str):
        raise ValueError(f"expected a string, got {type(s).__name__}: {s!r}")
    out = ['"']
    for ch in s:
        cp = ord(ch)
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ch == "\r":
            out.append("\\r")
        elif 0xD800 <= cp <= 0xDFFF:
            raise ValueError(f"string contains a lone surrogate U+{cp:04X}, "
                             f"which has no UTF-8 encoding: {s!r}")
        elif cp < 0x20 or cp == 0x7F:
            out.append(f"\\x{cp:02x}")
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def tql_lit(s):
    """A TypeQL string literal: JSON escaping, but characters kept as UTF-8
    rather than split into surrogate pairs."""
    return json.dumps(s, ensure_ascii=False)


# ------------------------------------------------------------ parse the schema
def _statements(text):
    """Split on `;` that are not inside a quoted string."""
    parts, buf, i = [], [], 0
    while i < len(text):
        m = re.compile(_QUOTED).match(text, i)
        if m:
            buf.append(m.group(0))
            i = m.end()
            continue
        if text[i] == ";":
            parts.append("".join(buf))
            buf = []
        else:
            buf.append(text[i])
        i += 1
    tail = "".join(buf).strip()
    if tail:
        raise UnsupportedSchema(f"schema text ends without `;`: {tail[:80]!r}")
    return [p.strip() for p in parts if p.strip()]


def _unquote(tok):
    try:
        v = json.loads(tok)
    except ValueError:
        raise UnsupportedSchema(f"cannot read the string literal {tok}") from None
    if not isinstance(v, str):
        raise UnsupportedSchema(f"not a string literal: {tok}")
    return v


_ANNOTATION = re.compile(r'@([A-Za-z_][A-Za-z0-9_-]*)'
                         r'(?:\(((?:' + _QUOTED + r'|[^()"])*)\))?')


def _clause(line):
    """(words before the first annotation, {annotation: argument text})."""
    m = re.search(r"@", re.sub(_QUOTED, lambda q: "x" * len(q.group(0)), line))
    head = line[:m.start()] if m else line
    tail = line[m.start():] if m else ""
    anns, pos = {}, 0
    while pos < len(tail):
        if tail[pos].isspace():
            pos += 1
            continue
        a = _ANNOTATION.match(tail, pos)
        if not a:
            raise UnsupportedSchema(f"cannot read the annotations in {line!r}")
        if a.group(1) in anns:
            raise UnsupportedSchema(f"annotation @{a.group(1)} twice in {line!r}")
        anns[a.group(1)] = a.group(2)
        pos = a.end()
    return head.split(), anns


def _card(arg, line):
    m = re.fullmatch(r"\s*(\d+)\s*\.\.\s*(\d*)\s*", arg or "")
    if not m:
        raise UnsupportedSchema(f"cannot read @card({arg}) in {line!r}")
    return int(m.group(1)), (int(m.group(2)) if m.group(2) else None)


def _only(anns, allowed, line):
    extra = set(anns) - set(allowed)
    if extra:
        raise UnsupportedSchema(
            f"unsupported annotation(s) {sorted('@' + a for a in extra)} in "
            f"{line!r}: the Lean types cannot represent them exactly")


def parse(type_schema):
    """Parse the canonical schema text returned by TypeDB's `type_schema()`.

    Strict: whatever this does not recognise is refused, because a statement
    or annotation skipped here is a difference between what TypeDB means and
    what the kernel will be told.
    """
    text = re.sub(r"^\s*define\b", "", type_schema.strip())
    attrs, types = {}, {}
    for stmt in _statements(text):
        lines = [l.strip().rstrip(",").strip() for l in stmt.splitlines()
                 if l.strip()]
        head, head_anns = _clause(lines[0])
        if len(head) != 2 or head[0] not in ("attribute", "entity", "relation"):
            raise UnsupportedSchema(f"unsupported schema statement {lines[0]!r}")
        kind, name = head
        _only(head_anns, {"abstract", "independent"}, lines[0])
        if name in attrs or name in types:
            raise UnsupportedSchema(f"{name!r} is defined twice")
        if kind == "attribute":
            a = {"value": None, "values": None, "sub": None}
            for l in lines[1:]:
                words, anns = _clause(l)
                if words[:1] == ["value"] and len(words) == 2:
                    _only(anns, {"values", "regex", "range"}, l)
                    a["value"] = words[1]
                    if "values" in anns:
                        vals = [_unquote(m.group(0)) for m in
                                re.finditer(_QUOTED, anns["values"] or "")]
                        if not vals:
                            raise UnsupportedSchema(f"empty @values in {l!r}")
                        a["values"] = vals
                elif words[:1] == ["sub"] and len(words) == 2 and not anns:
                    a["sub"] = words[1]
                else:
                    raise UnsupportedSchema(
                        f"unsupported clause {l!r} in attribute {name!r}")
            attrs[name] = a
            continue
        t = {"kind": kind, "abstract": "abstract" in head_anns, "sub": None,
             "roles": [], "owns": [], "plays": []}
        for l in lines[1:]:
            words, anns = _clause(l)
            if words[:1] == ["sub"] and len(words) == 2 and not anns:
                t["sub"] = words[1]
            elif words[:1] == ["relates"] and len(words) == 2 and kind == "relation":
                _only(anns, {"card"}, l)
                lo, hi = _card(anns["card"], l) if "card" in anns else (0, 1)
                t["roles"].append({"role": words[1], "one": (lo, hi) == (1, 1)})
            elif words[:1] == ["owns"] and len(words) == 2:
                _only(anns, {"key", "card", "unique", "values", "regex",
                             "range"}, l)
                if "key" in anns:
                    required = True
                elif "card" in anns:
                    lo, hi = _card(anns["card"], l)
                    if hi != 1:
                        # several values of one attribute cannot be one field
                        raise UnsupportedSchema(
                            f"{name}.{words[1]} is multi-valued (@card({anns['card']})); "
                            f"the generated types have no exact representation for it")
                    required = lo == 1
                else:
                    required = False        # TypeDB's default is @card(0..1)
                t["owns"].append({"attr": words[1], "required": required,
                                  "key": "key" in anns})
            elif words[:1] == ["plays"] and len(words) == 2 and not anns:
                t["plays"].append(words[1])
            else:
                raise UnsupportedSchema(
                    f"unsupported clause {l!r} in {kind} {name!r}")
        types[name] = t

    # attribute subtypes inherit their parent's value type and value set
    for name, a in attrs.items():
        seen, sup = {name}, a["sub"]
        while sup and (a["value"] is None or a["values"] is None):
            if sup not in attrs or sup in seen:
                raise UnsupportedSchema(f"attribute {name!r}: bad supertype {sup!r}")
            seen.add(sup)
            a["value"] = a["value"] or attrs[sup]["value"]
            a["values"] = a["values"] or attrs[sup]["values"]
            sup = attrs[sup]["sub"]
    # types inherit owns and roles from supertypes (TypeDB inheritance is single)
    for name, t in types.items():
        seen, sup = {name}, t["sub"]
        while sup:
            if sup not in types or sup in seen:
                raise UnsupportedSchema(f"{name!r}: bad supertype {sup!r}")
            seen.add(sup)
            have = {o["attr"] for o in t["owns"]}
            t["owns"] += [o for o in types[sup]["owns"] if o["attr"] not in have]
            roles = {r["role"] for r in t["roles"]}
            t["roles"] += [r for r in types[sup]["roles"] if r["role"] not in roles]
            sup = types[sup]["sub"]
    for t in types.values():
        for o in t["owns"]:
            if o["attr"] not in attrs:
                raise UnsupportedSchema(f"owns unknown attribute {o['attr']!r}")
    return {"attributes": attrs, "types": types}


def key_attr(model, tname):
    """The `@key` attribute of a type, or None.

    A role, on the Lean side, is the player's key as a string. So a rule that
    names a particular entity — "is this item the one named X?" — compiles to a
    comparison against that key, and both forms have to agree on which
    attribute that is.
    """
    keys = [o["attr"] for o in model["types"][tname]["owns"] if o.get("key")]
    return keys[0] if len(keys) == 1 else None


def role_player(model, relation, role):
    """The one type that plays `relation:role`, or None if it is not unique."""
    players = [n for n, t in model["types"].items()
               if f"{relation}:{role}" in t["plays"]]
    return players[0] if len(players) == 1 else None


def fields(model, tname):
    """[(typedb_name, lean_field, lean_type, how)] for a generated structure."""
    t, out = model["types"][tname], []
    for r in t["roles"]:
        out.append((r["role"], camel(r["role"]),
                    "String" if r["one"] else "List String", "role1" if r["one"] else "roleN"))
    for o in sorted(t["owns"], key=lambda o: o["attr"]):
        a = model["attributes"][o["attr"]]
        if a["values"]:
            if a["value"] != "string":
                raise UnsupportedSchema(
                    f"attribute {o['attr']!r}: @values on value {a['value']!r} "
                    f"has no Lean mapping")
            base, how = pascal(o["attr"]), "enum"
        elif a["value"] == "integer":
            # An ordering comparison is the point of having a number at all,
            # and `String` has no `≤` in Lean, so a threshold rule over a
            # string-typed quantity cannot be compiled — it has to be a real
            # `Int` here or the rule language can only test equality.
            base, how = "Int", "int"
        elif a["value"] in VALUE_TYPES:
            base, how = "String", "str"
        else:
            # boolean, double, decimal, date, datetime-tz, duration: as a
            # String these compare by spelling (`-0.0` ≠ `0.0`, `True` from
            # Python's str()), which is not what TypeDB means by them
            raise UnsupportedSchema(
                f"attribute {o['attr']!r} has value type {a['value']!r}, which "
                f"has no exact Lean mapping yet")
        out.append((o["attr"], camel(o["attr"]),
                    base if o["required"] else f"Option {base}",
                    how + ("" if o["required"] else "?")))
    names = [f for (_, f, _, _) in out]
    dup = {n for n in names if names.count(n) > 1}
    if dup:
        raise UnsupportedSchema(
            f"{tname}: TypeDB names {sorted(a for a, f, _, _ in out if f in dup)} "
            f"would all become the Lean field(s) {sorted(dup)}")
    return out


# --------------------------------------------------------------- generate Lean
def render(store, namespace, db=None):
    """The Lean module of types for the live schema: (source, model, hash)."""
    d = store.driver.databases.get(db or store.database)
    model = parse(d.type_schema())
    h = sha(d.schema())                       # types AND functions
    return _render(model, h, namespace), model, h


def _render(model, h, namespace):
    L = ["/-",
         "  GENERATED from the live TypeDB schema by attest/typebridge.py.",
         "  Do not edit: change the schema and regenerate.",
         f"  schema sha256 (types + functions): {h}",
         "-/",
         f"namespace {namespace}", "",
         f'def schemaSha256 : String := "{h}"', ""]
    type_names = {}

    def claim(lean_name, typedb_name):
        if lean_name in type_names:
            raise UnsupportedSchema(
                f"TypeDB types {type_names[lean_name]!r} and {typedb_name!r} "
                f"would both become the Lean type {lean_name!r}")
        type_names[lean_name] = typedb_name

    for an, a in sorted(model["attributes"].items()):
        if a["values"]:
            claim(pascal(an), an)
            ctors = [ctor(v) for v in a["values"]]
            if len(set(ctors)) != len(ctors):
                raise UnsupportedSchema(
                    f"attribute {an!r}: values {a['values']} would not all get "
                    f"distinct Lean constructors ({ctors})")
            L.append(f"/-- TypeDB `attribute {an}` @values -/")
            L.append(f"inductive {pascal(an)} | " + " | ".join(ctors))
            L.append("deriving DecidableEq, Repr\n")
    for tn, t in sorted(model["types"].items()):
        if t["abstract"]:
            continue
        fs = fields(model, tn)
        if not fs:
            continue
        claim(pascal(tn), tn)
        L.append(f"/-- TypeDB `{t['kind']} {tn}`"
                 + (f" (sub {t['sub']})" if t["sub"] else "") + " -/")
        L.append(f"structure {pascal(tn)} where")
        for (_, f, ty, _) in fs:
            L.append(f"  {f} : {ty}")
        L.append("deriving DecidableEq, Repr\n")
    L.append(f"end {namespace}\n")
    return "\n".join(L)


def generate(store, path, namespace, db=None):
    """Write the Lean types for the live schema to `path`, in `namespace`."""
    src, model, h = render(store, namespace, db)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(src)
    return model, h


def lean_literal(model, tname, row):
    """A TypeDB row (keys = TypeDB names) -> Lean `{ field := value, … }`.

    Strict, because the literal IS the data the kernel reasons about: every
    field of the generated type must be present (an absent optional is an
    explicit None), no key may be unknown, and each value must have the shape
    its field needs. A list role given a bare string, for instance, used to be
    split into its characters.
    """
    fs = fields(model, tname)
    known = {an for (an, _, _, _) in fs}
    unknown = set(row) - known
    if unknown:
        raise ValueError(f"{tname}: row has keys the type does not have: "
                         f"{sorted(unknown)}")
    missing = known - set(row)
    if missing:
        raise ValueError(f"{tname}: row lacks {sorted(missing)} (an absent "
                         f"optional value must be given as None)")
    parts = []
    for (an, f, ty, how) in fs:
        v = row[an]
        if how in ("role1", "str", "enum", "int") and v is None:
            raise ValueError(f"{tname}.{an} is required by the schema but missing")
        if how.endswith("?") and v is None:
            lit = "none"
        elif how in ("role1", "str", "str?"):
            lit = lean_str(_str(tname, an, v))
            lit = lit if how != "str?" else f"some {lit}"
        elif how == "roleN":
            if not isinstance(v, (list, tuple)):
                raise ValueError(f"{tname}.{an} is a list of role players; "
                                 f"got {type(v).__name__} {v!r}")
            lit = "[" + ", ".join(lean_str(_str(tname, an, x)) for x in v) + "]"
        elif how in ("enum", "enum?"):
            values = model["attributes"][an]["values"]
            if v not in values:
                raise ValueError(f"{tname}.{an} = {v!r} is not one of {values}")
            lit = "." + ctor(v) if how == "enum" else f"some .{ctor(v)}"
        elif how in ("int", "int?"):
            lit = _int(tname, an, v) if how == "int" else f"some {_int(tname, an, v)}"
        else:
            # Without this the loop kept the PREVIOUS field's literal and
            # wrote it under this field's name: a value the store never held,
            # in a proof term the kernel then accepted.
            raise ValueError(f"{tname}.{an}: no Lean literal for kind {how!r}")
        parts.append(f"{f} := {lit}")
    return "{ " + ", ".join(parts) + " }"


def _str(tname, an, v):
    if not isinstance(v, str):
        raise ValueError(f"{tname}.{an} must be a string; the store returned "
                         f"{v!r} ({type(v).__name__})")
    return v


def _int(tname, an, v):
    """A Lean `Int` literal. Parenthesised when negative, since `x := -1` is
    fine but `some -1` is not."""
    if isinstance(v, bool) or not isinstance(v, int):
        raise ValueError(
            f"{tname}.{an} is `value integer` in the schema but the store "
            f"returned {v!r} ({type(v).__name__})")
    return f"({v})" if v < 0 else str(v)


# ---------------------------------------------------- artifacts in TypeDB
def tql_str(text) -> str:
    """A TypeQL string literal for arbitrary text, including Lean sources.

    ONE definition. There were two: this one escaped only backslash and
    quote and left control characters raw, while `runner.tql_str` used
    `json.dumps(..., ensure_ascii=False)`. Both happened to work — TypeQL
    tolerates a multi-line string — but the same job answered two ways will
    drift, and only one of them was reviewed when the bridge was hardened.
    The surviving one escapes control characters explicitly and keeps
    characters UTF-8: plain `json.dumps` splits anything outside the Basic
    Multilingual Plane into surrogate halves, which Lean 4 reads as U+0000,
    and that is how two different emoji were once proved equal.
    """
    return json.dumps(str(text), ensure_ascii=False)


def publish(store, sources, recorded_at):
    """Store each source as an artifact keyed by its hash (idempotent).

    `sources` is [(name, kind, path)] — a Lean module name or a rule file.
    """
    ids = {}
    for module, kind, path in sources:
        src = open(path).read()
        h = sha(src)
        aid = f"{module}@{h[:12]}"
        if not store.rows(f'match $a isa artifact, has artifact-id {tql_str(aid)}; select $a;'):
            store.write(
                f'insert $a isa artifact, has artifact-id {tql_str(aid)}, '
                f'has artifact-kind {tql_str(kind)}, '
                f'has lean-module {tql_str(module)}, '
                f'has lean-source {tql_str(src)}, '
                f'has source-sha256 {tql_str(h)}, '
                f'has recorded-at {recorded_at};')
        # Keyed by artifact id, not by kind. Keying by kind silently kept
        # ONE artifact per kind, so a domain with two theorem modules
        # published both and cited only the last: its decisions could never
        # be re-checked against the other one.
        ids[aid] = kind
    return ids


class OutOfSync(Exception):
    pass


def types_match(store, stored, namespace, db=None):
    """Do the LIVE schema's types still render to `stored`?

    The question `recheck` has to ask is about types, not about the whole
    schema. `render` embeds a hash of `d.schema()`, which covers types AND
    functions, so comparing whole files answered a different question: one
    extra deployed function changed two lines and nothing else. Since `sync`
    deploys a function per rule, and the function's name carries the rule's
    hash, editing or adding ANY rule made every earlier decision report that
    the schema it cites no longer renders — re-verification broken by an
    unrelated change. The examples never saw it because they sync every rule
    before deciding anything.

    So the stored file's own hash line is reused for the comparison, which
    isolates the types: a difference now means the types really did move.
    Returns (ok, model, why).
    """
    d = store.driver.databases.get(db or store.database)
    model = parse(d.type_schema())
    m = re.search(r'def schemaSha256 : String := "([0-9a-f]{64})"', stored)
    if not m:
        return False, model, "the stored types artifact carries no schema hash"
    as_stored = _render(model, m.group(1), namespace)
    if as_stored == stored:
        return True, model, None
    return False, model, ("the live schema's types no longer render to the "
                          "Lean types this decision cites")


def check_sync(store, schema_lean, sources, namespace, db=None):
    """The Lean types on disk are EXACTLY what the live schema renders to, and
    every source in use is published in TypeDB. Returns the artifact ids to
    cite in certificates.

    Comparing only the `schemaSha256` line inside the file is not enough: the
    rest of the file can be edited (an instance that changes how a numeral
    reads, a field type) while that line is kept, and once the edited file is
    published it passes. The rule module is held to byte equality with its
    compiler's output; the type module is held to the same standard.
    """
    expected, _model, live = render(store, namespace, db)
    on_disk = open(schema_lean).read()
    if on_disk != expected:
        m = re.search(r'def schemaSha256 : String := "([0-9a-f]{64})"', on_disk)
        why = ("its schema hash differs" if not m or m.group(1) != live else
               "its body differs from what the schema renders to, though its "
               "hash line matches")
        raise OutOfSync(f"{schema_lean} is not the Lean rendering of the live "
                        f"TypeDB schema ({live[:12]}): {why}. Regenerate it.")
    ids = {}
    for module, kind, path in sources:
        h = sha(open(path).read())
        aid = f"{module}@{h[:12]}"
        if not store.rows(f'match $a isa artifact, has artifact-id {tql_str(aid)}, '
                          f'has source-sha256 {tql_str(h)}; select $a;'):
            raise OutOfSync(f"{module} ({h[:12]}) is not published in TypeDB")
        # Keyed by artifact id, not by kind. Keying by kind silently kept
        # ONE artifact per kind, so a domain with two theorem modules
        # published both and cited only the last: its decisions could never
        # be re-checked against the other one.
        ids[aid] = kind
    return ids


_MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")


def materialize(store, artifact_ids, lean_dir, root_module, workdir=None):
    """Write the artifacts' Lean sources (from TypeDB) into a fresh Lake
    workspace and build it. Returns the workspace path.

    Module names come from the store, so they are validated before they become
    paths: a name with a `/` or `..` in it used to write a `.lean` file outside
    the workspace — for instance over a domain's own Schema.lean.
    """
    if not _MODULE.match(root_module):
        raise OutOfSync(f"invalid root module name {root_module!r}")
    workdir = workdir or tempfile.mkdtemp(prefix="attest-recheck-")
    os.makedirs(workdir, exist_ok=True)
    root = os.path.realpath(workdir)
    shutil.copy(os.path.join(lean_dir, "lakefile.lean"), workdir)
    # The toolchain pin, too. Only the lakefile was copied, so the rebuilt
    # workspace ran on whatever elan defaults to globally rather than the
    # version the decision was checked with — which can be a Lean older
    # than 4.32.2, where the kernel admits `False` with no axioms at all
    # (CVE-2026-72844). A recheck on that toolchain accepts anything while
    # reporting a clean axiom list. Measured on this machine: the default is
    # 4.15.0 and the packages pin 4.35.0.
    pin = os.path.join(lean_dir, "lean-toolchain")
    if os.path.exists(pin):
        shutil.copy(pin, workdir)
    else:
        raise OutOfSync(
            f"{lean_dir} has no lean-toolchain, so a rebuilt workspace "
            f"would be checked by an unpinned Lean")
    mods = []
    for aid in artifact_ids:
        r = store.rows(f'match $a isa artifact, has artifact-id {tql_str(aid)}, '
                       f'has lean-module $m, has lean-source $s, '
                       f'has artifact-kind $k, has source-sha256 $h; '
                       f'select $m, $s, $k, $h;')
        if not r:
            raise OutOfSync(f"artifact {aid} not found in TypeDB")
        r = r[0]
        if sha(r["s"]) != r["h"]:
            raise OutOfSync(f"artifact {aid} source does not match its hash")
        # Select on KIND, not on the shape of the name. The first version
        # skipped anything containing "/", which silently mis-handled a rule
        # source whose id has dots but no slash, such as `a.b.rule`: it was
        # taken for a Lean module and split on its dots into `a/b/.lean`.
        # The workspace then failed to build, and the failure read as "the
        # artifacts are bad" rather than "we wrote a nonsense path".
        if r.get("k") not in LEAN_KINDS:
            continue
        if not _MODULE.match(r["m"]):
            raise OutOfSync(f"artifact {aid} names an invalid Lean module "
                            f"{r['m']!r}")
        path = os.path.realpath(os.path.join(workdir, *r["m"].split(".")) + ".lean")
        if not path.startswith(root + os.sep):
            raise OutOfSync(f"artifact {aid} would be written outside the workspace")
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(r["s"])
        mods.append(r["m"])
    with open(os.path.join(workdir, f"{root_module}.lean"), "w") as f:
        f.write("".join(f"import {m}\n" for m in sorted(mods)))
    out = subprocess.run(["lake", "build"], cwd=workdir, capture_output=True, text=True,
                         timeout=900)
    if out.returncode != 0:
        raise OutOfSync("artifacts from TypeDB do not build:\n"
                        + (out.stdout + out.stderr)[-1200:])
    return workdir
