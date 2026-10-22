"""Rule compiler: ONE expert-readable rule file -> Lean definition + TypeQL function.

Core: nothing domain-specific. Paths and namespaces come from the caller, so a
domain's rules and Lean package can live outside this repository.


    <name>.rule ──compile──┬──> <LeanDir>/<Rules>/<Name>.lean   (the authority)
                           └──> TypeQL `fun` defined in TypeDB   (fast, untrusted search)

Both outputs embed the rule source's sha256. Before every decision,
`check(store, rule)` recompiles the rule and requires that
  - the Lean file in use is byte-identical to the compiler's Lean output, and
  - the function stored in TypeDB is identical (modulo whitespace) to the
    compiler's TypeQL output,
so the two can only differ if the compiler itself is wrong, and that is what
the per-case differential check (TypeDB search vs Lean verdict) still watches.

Rule language (line-based):
    rule <id> <version>
    says "<plain-language statement>"
    subject <entity type>
    parameter <name> : <entity type>          (zero or more further inputs)
    collection <name> : <relation type> [for (subject | <parameter>) via <role>]
    closure <name> over <collection> from <role> to <role>
    conclude <Name> when
      some <relation type> <var> in <collection>
      require <var>.<field> (= | != | is-a <closure>) <var>.<field> | <literal>

`require x.f is-a y.g` means: x.f is y.g, or reaches y.g through the closure.
"""
import hashlib, json, os, re

from . import typebridge as tb


class RuleError(Exception):
    pass


#: one sha-256 helper, defined in `typebridge`. This module's own copy took
#: only `str` and would raise on bytes, which is the sort of difference two
#: implementations of one job acquire.
sha = tb.sha


# --------------------------------------------------------------------- parse
def _strip_comment(line: str) -> str:
    """Remove a `#` comment, but not a `#` inside a quoted literal.

    Splitting on the first `#` cut literals in half. `require m.source =
    "ICD#10"` compiled to a comparison against `"ICD` — truncated AND with
    an unbalanced quote — in BOTH the Lean definition and the TypeQL search.
    Because both sides were cut identically they agreed, so the per-case
    comparison of search against kernel could never see it: the rule simply
    asked a different question than the one written down.
    """
    out, quoted = [], False
    for ch in line:
        if ch == '"':
            quoted = not quoted
        elif ch == "#" and not quoted:
            break
        out.append(ch)
    return "".join(out)


def parse(text):
    r = {"collections": [], "closures": [], "params": [], "steps": [],
         "source": text, "sha": sha(text)}
    in_body = False
    # Nested blocks are tracked by indentation. `stack[-1]` is the step list
    # the next, more-indented line belongs to; -1 is the outermost body.
    stack = [(-1, r["steps"])]
    for n, raw in enumerate(text.splitlines(), 1):
        line = _strip_comment(raw).rstrip()
        if not line.strip():
            continue
        w = line.split()
        try:
            if in_body and raw[:1].isspace():
                indent = len(raw) - len(raw.lstrip())
                while len(stack) > 1 and indent <= stack[-1][0]:
                    stack.pop()
                here = stack[-1][1]
                if w[0] == "some":                       # some <type> <var> in <collection>
                    _, ty, var, kw, coll = w
                    assert kw == "in"
                    here.append({"kind": "some", "type": ty, "var": var, "coll": coll})
                elif w[0] == "require":
                    # the operator is a comparison, `is-a`, or the NAME of a
                    # declared closure — which is how a rule says which
                    # hierarchy it means when it walks more than one
                    m = re.match(
                        r"require\s+(\S+)\s+"
                        r"(=|!=|>=|<=|>|<|[A-Za-z_][A-Za-z0-9_'-]*)\s+"
                        r"(\S+(?:\s*[-+]\s*\d+)?)$", line.strip())
                    assert m, ("expected: require <lhs> "
                               "(=|!=|>=|<=|>|<|is-a|<closure>) <rhs>")
                    rhs = m.group(3)
                    # A quoted literal must be ONE balanced literal. The
                    # body is tokenised on whitespace, so `"a b"` and `"a.b"`
                    # already failed — but with errors about something else
                    # entirely ("a is used before it is bound"). Worse,
                    # `"a"b"` parsed clean and was emitted verbatim into both
                    # the Lean definition and the TypeQL function, where the
                    # stray quote ends the literal early. Refuse here, where
                    # the rule author can see which line is at fault.
                    if '"' in rhs and not re.fullmatch(r'"[^"]*"', rhs):
                        raise AssertionError(
                            f"{rhs!r} is not a single balanced literal. A "
                            f"quoted literal may not contain a quote, and "
                            f"the rule body is read one token per word, so "
                            f"it may not contain a space or a dot either")
                    here.append({"kind": "require", "lhs": m.group(1),
                                 "op": m.group(2), "rhs": rhs})
                elif w[0] == "none":                     # none of  <indented block>
                    assert w[1:] == ["of"], "expected: none of"
                    block = {"kind": "none", "steps": []}
                    here.append(block)
                    stack.append((indent, block["steps"]))
                else:
                    raise AssertionError(f"unknown body line {w[0]!r}")
                continue
            in_body = False
            stack = [(-1, r["steps"])]
            if w[0] == "rule":
                r["id"], r["version"] = w[1], w[2]
            elif w[0] == "says":
                r["says"] = json.loads(line.strip()[len("says"):].strip())
            elif w[0] == "subject":
                r["subject"] = w[1]
            elif w[0] == "collection":            # collection <name> : <type> [for <scope> via <role>]
                c = {"name": w[1], "type": w[3], "via": None, "scope": None}
                assert w[2] == ":"
                if len(w) > 4:
                    assert w[4] == "for" and w[6] == "via" and len(w) == 8, \
                        "expected: for (subject | <parameter>) via <role>"
                    c["scope"], c["via"] = w[5], w[7]
                r["collections"].append(c)
            elif w[0] == "parameter":             # parameter <name> : <entity type>
                assert len(w) == 4 and w[2] == ":", \
                    "expected: parameter <name> : <entity type>"
                r["params"].append({"name": w[1], "type": w[3]})
            elif w[0] == "closure":               # closure <name> over <coll> from <role> to <role>
                assert w[2] == "over" and w[4] == "from" and w[6] == "to"
                r["closures"].append({"name": w[1], "coll": w[3], "from": w[5], "to": w[7]})
            elif w[0] == "conclude":              # conclude <Name> when
                assert w[2] == "when"
                r["conclusion"], in_body = w[1], True
            else:
                raise AssertionError(f"unknown line {w[0]!r}")
        except (AssertionError, IndexError, ValueError) as e:
            raise RuleError(f"line {n}: {raw.strip()!r}: {e}")
    _check(r)
    return r


_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")

#: a TypeDB label or a rule-local name: identifiers may carry hyphens
#: (`member-of`, `effective-day`), which Lean identifiers may not
_TYPE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*$")


def _safe_prose(text):
    """Prose that cannot escape a Lean comment.

    `says` is interpolated into `/- … -/` and `/-- … -/` in the generated
    module. A value containing `-/` and a newline closes the comment and the
    rest is elaborated as Lean — verified to reach `initialize`, i.e. code
    execution at build time, from a field a domain expert writes as a
    sentence. The drift check does not help: the generated file genuinely is
    what the rule compiles to.
    """
    if "-/" in text or "/-" in text:
        raise RuleError("`says` may not contain a Lean comment delimiter")
    if "\n" in text or "\r" in text:
        raise RuleError("`says` must be a single line")
    return text


def all_steps(steps):
    """Every step, descending into `none of` blocks.

    A check that iterates only the top level silently exempts whatever is
    written inside a negation — which is where a rule hides its hardest
    conditions.
    """
    for s in steps:
        yield s
        if s["kind"] == "none":
            yield from all_steps(s["steps"])


_PARAM_RE = re.compile(r"^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$")


def _check_params(r):
    """Parameters: further inputs of a decision, beyond its subject.

    A rule about one *pair* — this order for this sample, this route of this
    pathway — used to have to invent an entity whose key spelled the pair
    ("s000001:chest-xray"), because a rule's only input was its subject. A
    parameter is that second input, named and typed, and a collection can be
    scoped to it exactly as to the subject. Both compiled forms take it: the
    Lean snapshot carries its key and every binder scoped to it checks it;
    the TypeQL search takes it as an argument.
    """
    names = [p["name"] for p in r["params"]]
    if len(set(names)) != len(names):
        raise RuleError("a parameter is declared twice")
    lean_names = {c["name"] for c in r["collections"]} | {"subject", "asOfDay"}
    for p in r["params"]:
        if not _PARAM_RE.match(p["name"]) or p["name"] == "subject":
            raise RuleError(
                f"parameter {p['name']!r}: use lower-case letters, digits "
                f"and single hyphens, and not `subject`")
        if tb.camel(p["name"]) in lean_names or p["name"] in lean_names:
            raise RuleError(
                f"parameter {p['name']!r} collides with a collection or a "
                f"field the compiled snapshot already has")
    for c in r["collections"]:
        if c["scope"] not in (None, "subject", *names):
            raise RuleError(
                f"collection {c['name']}: `for {c['scope']}` names neither "
                f"the subject nor a declared parameter")


#: `rule <id> <version>` — a dotted path of identifiers, and a version
_RULE_ID_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*(\.[A-Za-z_][A-Za-z0-9_-]*)*$")
_VERSION_RE = re.compile(r"^[A-Za-z0-9_.-]+$")


def _check_names(r):
    """Every identifier field, before any of them reaches a generated file.

    `says` was guarded by `_safe_prose` because it is interpolated into a
    Lean comment. The other fields are interpolated into the same file and
    were not guarded at all: `rule demo.x v0.1"++"-/initialize` put a
    comment delimiter into the header and the `ruleId` string literal,
    closing the comment early and reaching `initialize` — build-time code
    execution, from a field nobody thinks of as code. Collection, binder,
    closure, parameter and subject names reach the generated structures the
    same way. The drift check is no defence: the generated file genuinely is
    what the rule compiles to.
    """
    if not _RULE_ID_RE.match(r["id"]):
        raise RuleError(
            f"rule id {r['id']!r} must be dot-separated identifiers")
    if not _VERSION_RE.match(r["version"]):
        raise RuleError(
            f"rule version {r['version']!r} must be letters, digits, "
            f"'.', '-' or '_'")
    if not _IDENT_RE.match(r["subject"]) and not _TYPE_RE.match(r["subject"]):
        raise RuleError(f"subject {r['subject']!r} is not a type name")
    for c in r["collections"]:
        for field in ("name", "type", "via", "scope"):
            value = c.get(field)
            if value is None:
                continue
            if not _TYPE_RE.match(value):
                raise RuleError(
                    f"collection {c['name']!r}: {field} {value!r} is not a "
                    f"name")
    for c in r["closures"]:
        for field in ("name", "coll", "from", "to"):
            if not _TYPE_RE.match(c[field]):
                raise RuleError(
                    f"closure {c['name']!r}: {field} {c[field]!r} is not a "
                    f"name")
    for prm in r["params"]:
        for field in ("name", "type"):
            if not _TYPE_RE.match(prm[field]):
                raise RuleError(
                    f"parameter {prm['name']!r}: {field} {prm[field]!r} is "
                    f"not a name")
    for s in all_steps(r["steps"]):
        if s["kind"] == "some":
            for field in ("type", "var", "coll"):
                if not _TYPE_RE.match(s[field]):
                    raise RuleError(
                        f"`some {s['type']} {s['var']} in {s['coll']}`: "
                        f"{field} {s[field]!r} is not a name")


def _check(r):
    _safe_prose(r["says"])
    _check_names(r)
    _check_params(r)
    # An empty body compiles to `Prop := True` (see `build` in compile_lean):
    # vacuously provable, and on an `Eligible`-style conclusion that approves
    # everyone with a real kernel proof.
    if not any(s["kind"] == "some" for s in r["steps"]):
        raise RuleError("a rule body needs at least one `some` step")
    # The conclusion is interpolated into a theorem statement, so it has to
    # be a name and nothing else.
    if not _IDENT_RE.match(r["conclusion"]):
        raise RuleError(
            f"conclusion {r['conclusion']!r} is not a Lean identifier")
    # Resolve the closure each walking step means, once, here — so both
    # compilers read it off the step instead of each guessing closures[0].
    # Guessing was why more than one closure used to be refused outright:
    # the two compiled forms would have been wrong in exactly the same way,
    # which the per-case differential cannot see.
    declared = {c["name"] for c in r["closures"]}
    for s in all_steps(r["steps"]):
        if s["kind"] != "require" or s["op"] in COMPARISONS:
            continue
        if s["op"] in declared:
            s["closure"] = s["op"]
        elif s["op"] == "is-a":
            if not declared:
                raise RuleError("is-a used but no closure declared")
            if len(declared) > 1:
                raise RuleError(
                    f"`require {s['lhs']} is-a {s['rhs']}` does not say which "
                    f"closure it means, and {len(declared)} are declared "
                    f"({', '.join(sorted(declared))}): name one as the "
                    f"operator, e.g. `require {s['lhs']} "
                    f"{sorted(declared)[0]} {s['rhs']}`")
            s["closure"] = next(iter(declared))
        else:
            raise RuleError(
                f"`require {s['lhs']} {s['op']} {s['rhs']}`: {s['op']!r} is "
                f"neither a comparison nor a declared closure"
                + (f" ({', '.join(sorted(declared))})" if declared else ""))
    colls = {c["name"]: c for c in r["collections"]}
    closures = {c["name"] for c in r["closures"]}
    bound = {}

    def walk(steps, visible, negated):
        """Check one block. `visible` is what is in scope here; a binder
        inside `none of` is local to it, exactly as in both compiled forms."""
        for s in steps:
            if s["kind"] == "none":
                if not any(x["kind"] == "some" for x in s["steps"]):
                    # `none of` with no binder is `¬ True` or `¬ <condition
                    # on outer variables>`: either a constant or a plain
                    # negated require written the long way round.
                    raise RuleError(
                        "`none of` needs at least one `some` step: with none "
                        "it is not a statement about absence")
                walk(s["steps"], dict(visible), True)
                continue
            if s["kind"] == "some":
                if s["coll"] not in colls or colls[s["coll"]]["type"] != s["type"]:
                    raise RuleError(f"`some {s['type']} {s['var']} in {s['coll']}`: "
                                    f"no such collection of that type")
                # `$<var>_<field>` is how the search names a bound field,
                # so a binder containing `_` can collide with one: a rule
                # binding both `e` and `e_note` and reading `e.note`
                # compiles to two different uses of `$e_note`, and the
                # search then asserts a relation IS a string and can never
                # match. Lean is unaffected, so every positive case is
                # refused as DISAGREE and every negative one recorded as
                # "agree".
                if (s["var"] in RESERVED_BINDERS
                        or re.fullmatch(r"(?:[cdk]|arg)\d+", s["var"])
                        or re.search(r"_(ra|rx|fid)$", s["var"])
                        or "_" in s["var"]):
                    # Both compilers introduce names of their own: `s` is the
                    # snapshot in every Lean definition; `$subject`, `$t`,
                    # `$asof_day`, `$c1`, `$d1`, `$k1` and `$v_ra`/`$v_rx`/
                    # `$v_fid` are the witness function's. A binder spelled the
                    # same failed deep inside `lake build` or `define` with an
                    # error about a variable the author never wrote.
                    raise RuleError(
                        f"`some … {s['var']} …`: {s['var']!r} is a name the "
                        f"compiled forms use themselves (an underscore makes "
                        f"it collide with `$<var>_<field>`); pick another "
                        f"binder")
                if s["var"] in visible:
                    # Lean shadows the first binder, so the two are independent
                    # records; TypeQL binds the same name to the same record. The
                    # compiler would emit two different rules from one source —
                    # drift manufactured by the thing that exists to prevent it.
                    raise RuleError(
                        f"`some … {s['var']} …` binds {s['var']!r} twice: the "
                        f"two compiled forms would not agree")
                visible[s["var"]] = s
                # every binder's type is needed to resolve `v.field` later,
                # whichever block it was bound in
                bound[s["var"]] = s
                continue
            if "." not in s["lhs"] and "." not in s["rhs"]:
                # compile_lean would emit `"a" ≠ "b"` — trivially true, so
                # the condition silently disappears from the authority
                raise RuleError(
                    f"`require {s['lhs']} {s['op']} {s['rhs']}` compares two "
                    f"literals; it would compile to a constant")
            if "." not in s["lhs"]:
                raise RuleError(
                    f"`require {s['lhs']} …`: put the field on the left "
                    f"(`{s['rhs']} {s['op']} {s['lhs']}`)")
            for side in ("lhs", "rhs"):
                v = s[side].split(".")[0]
                if "." in s[side] and v not in visible:
                    raise RuleError(f"`require {s['lhs']} {s['op']} {s['rhs']}`: "
                                    f"{v} is used before it is bound")
            if s["op"] == "is-a" and not closures:
                raise RuleError("is-a used but no closure declared")

    walk(r["steps"], {}, False)
    r["vars"] = bound


# ------------------------------------------------------------- field typing
def _field(model, ty, f):
    """(lean field, how) for <relation type>.<field>.

    `how` is the kind the type bridge reports — `role1`, `roleN`, `enum`,
    `int`, `str`, and the `?` forms for an optional attribute — not a
    coarser label. An earlier version collapsed every attribute to `attr`,
    which left the compilers unable to tell a number from a string: a
    threshold comparison then looked like a comparison of two opaque values
    and the numeric check could never fire.
    """
    for (an, lf, lty, how) in tb.fields(model, ty):
        if an == f:
            return lf, how
    raise RuleError(f"{ty} has no role or attribute {f!r}")


#: The instant the decision is being made, as a whole number of days. It is
#: the one quantity a rule may use that is not in the snapshot's facts, and
#: every rule about a time window needs it: "within six months" and "for at
#: least three months" are statements about now, not about the record.
#:
#: Both compiled forms get the SAME number, computed once by the runner
#: (`as_of_day`), so the Lean definition and the TypeQL search cannot drift
#: on the definition of a day or a timezone.
AS_OF_DAY = "as-of-day"
_AS_OF_RE = re.compile(rf"^{AS_OF_DAY}(?:\s*([-+])\s*(\d+))?$")


def _side(r, model, expr):
    """Classify one side of a require.

    ('field', var, field, lean, how) · ('lit', value) · ('asof', offset)
    """
    expr = expr.strip()
    m = _AS_OF_RE.match(expr)
    if m:
        offset = int(m.group(2) or 0) * (-1 if m.group(1) == "-" else 1)
        return ("asof", offset)
    if "." in expr:
        v, f = expr.split(".", 1)
        lf, how = _field(model, r["vars"][v]["type"], f)
        return ("field", v, f, lf, how)
    return ("lit", expr.strip('"'))


def uses_as_of(r) -> bool:
    """Whether any comparison in the rule mentions `as-of-day`."""
    return any(_AS_OF_RE.match(s[side].strip())
               for s in all_steps(r["steps"]) if s["kind"] == "require"
               for side in ("lhs", "rhs"))


#: The ONLY `set_option` lines a generated rule module may carry. Each raises
#: an elaboration search budget and none changes what the kernel will accept
#: — unlike, say, `debug.skipKernelTC`, which would make a proof that was
#: never checked look checked. Keeping the set closed and asserting it in the
#: offline tests stops the generated-rule channel becoming a way to smuggle
#: a dangerous option past `kernel.forbidden`, which only scans case files
#: and stored proofs.
#:
#: There was one of these per budget Lean offers; at 4.35 the search size
#: alone is enough, and the two dropped included
#: `synthInstance.maxHeartbeats` — the only TIME-based option here. A
#: time-based budget makes elaboration depend on machine speed and load, so
#: the same stored proof can re-verify on one box and fail on another, and a
#: false audit failure is indistinguishable from a real one. What remains is
#: a deterministic bound on search size.
SAFE_OPTIONS = (
    "set_option synthInstance.maxSize 2000 in",
)

#: Operators that compare two values, as opposed to walking a closure.
#: binder names the compiled forms already use (see `_check`)
RESERVED_BINDERS = frozenset({"s", "t", "subject", "asof_day"})

COMPARISONS = {"=", "!=", ">=", "<=", ">", "<"}
#: Comparisons that need an ordering, so both sides must be numbers.
ORDERING = {">=", "<=", ">", "<"}
#: Lean and TypeQL spellings of every operator the language has.
LEAN_OP = {"=": "=", "!=": "≠", ">=": "≥", "<=": "≤", ">": ">", "<": "<"}
TQL_OP = {"=": "==", "!=": "!=", ">=": ">=", "<=": "<=", ">": ">", "<": "<"}


def _is_int_literal(text):
    return re.fullmatch(r"-?\d+", text.strip()) is not None


def _reject_bad_comparison(r, model):
    """Refuse a comparison the two compilers would not agree on.

    An ordering on a string is the dangerous case: TypeQL compares strings
    lexicographically and would happily answer, while Lean's `String` has no
    `≤`, so the generated module does not build. Fail closed is better than
    fail open, but it fails as a Lean build error about generated code, which
    reads as a compiler bug rather than a rule that cannot mean what it says.
    """
    for s in all_steps(r["steps"]):
        if s["kind"] != "require" or s["op"] not in COMPARISONS:
            continue
        a = _side(r, model, s["lhs"])
        b = _side(r, model, s["rhs"])
        kinds = [x[4] for x in (a, b) if x[0] == "field"]
        numeric = [k in ("int", "int?") for k in kinds]
        where = f"`require {s['lhs']} {s['op']} {s['rhs']}`"
        if any(x[0] == "asof" for x in (a, b)) and not all(numeric):
            raise RuleError(
                f"{where} compares {AS_OF_DAY} with something that is not a "
                f"`value integer` attribute; {AS_OF_DAY} is a whole number "
                f"of days")
        if any(k.endswith("?") for k in kinds):
            raise RuleError(
                f"{where} compares an optional attribute; the rule has to say "
                f"what an absent value means before it can be compared")
        if s["op"] in ORDERING:
            if not all(numeric):
                raise RuleError(
                    f"{where} orders a non-numeric value: only `value "
                    f"integer` attributes can be compared with "
                    f"{sorted(ORDERING)}")
            if b[0] == "lit" and not _is_int_literal(b[1]):
                raise RuleError(f"{where}: {b[1]!r} is not an integer")
        elif any(numeric):
            # `=` between a number and a string compiles to `70 = "70"` in
            # Lean (a type error) and to a working comparison in TypeQL.
            if not all(numeric) and b[0] == "field":
                raise RuleError(
                    f"{where} compares a number with a non-number")
            if b[0] == "lit" and not _is_int_literal(b[1]):
                raise RuleError(
                    f"{where}: {s['lhs']} is an integer attribute, so "
                    f"{b[1]!r} has to be an integer")


# ------------------------------------------------------------------ to Lean
def role_key(r, model, side):
    """The key attribute to compare a named entity against, for a role side.

    Naming a particular entity — "is this item the one named X?", "does
    this code fall under group Y?" — is a basic shape for a
    rule, and the two compiled forms mean different things unless this is
    done deliberately. On the Lean side a role IS the player's key, so the
    comparison is already a string one. On the TypeQL side the role binds
    the ENTITY, so comparing it to a string compares an entity to a string:
    `define` fails, or worse it succeeds meaning something else.

    So TypeQL is made to compare the same thing Lean does — the player's
    key. That needs the role to have exactly one player type and that type
    exactly one `@key`; without both there is no single value the two forms
    could agree on, and the rule is refused instead of guessed at.
    """
    if side[0] != "field":
        return None
    if not side[4].startswith("role"):
        # A closure walks between ENTITIES, so its operand has to be a role.
        # Applied to an attribute it produced valid Lean and a TypeQL
        # `define` carrying the literal text `has None`, failing at deploy
        # with an error naming `None` rather than naming the rule line.
        raise RuleError(
            f"`{side[1]}.{side[2]}` is an attribute, not a role: a closure "
            f"walks between entities, so it cannot start from one")
    relation = r["vars"][side[1]]["type"]
    player = tb.role_player(model, relation, side[2])
    if player is None:
        raise RuleError(
            f"`{side[1]}.{side[2]}` is played by no single type, so naming an "
            f"entity here has no one key to compare against")
    key = tb.key_attr(model, player)
    if key is None:
        raise RuleError(
            f"`{side[1]}.{side[2]}` is played by {player}, which has no single "
            f"`@key`: there is no value the Lean rule and the TypeQL search "
            f"would both compare")
    return key


def _reject_role_vs_literal(r, model):
    """Check that every role-vs-name comparison can be compiled soundly.

    `role_key` raises when it cannot be. A roleN (`@card` above one) is still
    refused outright: in Lean it is a list of keys, so `=` against one name
    is a type error rather than the membership test the author meant.
    """
    for s in all_steps(r["steps"]):
        if s["kind"] != "require":
            continue
        for lhs, rhs in ((s["lhs"], s["rhs"]), (s["rhs"], s["lhs"])):
            if "." not in lhs or "." in rhs:
                continue
            side = _side(r, model, lhs)
            if not side[4].startswith("role"):
                continue
            if side[4] == "roleN":
                raise RuleError(
                    f"`require {s['lhs']} {s['op']} {s['rhs']}` names one "
                    f"entity but `{side[1]}.{side[2]}` holds several: say "
                    f"which one, or compare a single-valued role")
            role_key(r, model, side)


def scoped(r):
    """Whether any collection is scoped to the decision's subject."""
    return any(c["via"] and c["scope"] in (None, "subject")
               for c in r["collections"])


def scope_field(collection):
    """The snapshot field a scoped collection's rows must match: the
    subject, or the parameter the collection is scoped to."""
    sc = collection.get("scope") or "subject"
    return "subject" if sc == "subject" else tb.camel(sc)


def scope_var(r, collection):
    """The TypeQL variable for a scoped collection's scope."""
    sc = collection.get("scope") or "subject"
    if sc == "subject":
        return "$subject"
    return f"$arg{[p['name'] for p in r['params']].index(sc)}"


def scope_type(r, collection):
    sc = collection.get("scope") or "subject"
    if sc == "subject":
        return r["subject"]
    return next(p["type"] for p in r["params"] if p["name"] == sc)


def binder_guards(step, colls):
    """The conjuncts every `some` carries beyond the rule's own conditions.

    Both of these were checked by the compiled TypeQL search and by nothing
    in the authority, so the kernel's statement was weaker than the search's
    question — the one asymmetry a per-case differential cannot report,
    because both forms agree on every snapshot the export actually builds.
    """
    collection = colls[step["coll"]]
    out = []
    if collection.get("via"):
        out.append(f"{step['var']}.{tb.camel(collection['via'])} = "
                   f"s.{scope_field(collection)}")
    out.append(f"{step['var']}.retractedAt = none")
    return out


def compile_lean(r, model, rules_namespace, schema_namespace):
    _reject_role_vs_literal(r, model)
    _reject_bad_comparison(r, model)
    colls = {c["name"]: c for c in r["collections"]}
    L = ["/-",
         f"  GENERATED from rule {r['id']} by attest/rulec.py. Do not edit.",
         f"  rule {r['id']} {r['version']}",
         f"  {r['says']}",
         f"  rule source sha256: {r['sha']}",
         "-/",
         f"import {schema_namespace}", "",
         f"namespace {module(r, rules_namespace)}",
         f"open {schema_namespace}", "",
         f'def ruleId : String := "{r["id"]} {r["version"]}"',
         f'def ruleSha256 : String := "{r["sha"]}"', "",
         "/-- What one case may look at: values of the types generated from TypeDB. -/",
         "structure Snapshot where"]
    for c in r["collections"]:
        L.append(f"  {c['name']} : List {tb.pascal(c['type'])}")
    if scoped(r):
        # The authority used to say nothing about WHOSE facts these are.
        # `collection X : T for subject via R` compiled into the TypeQL
        # search only, so the kernel-checked statement was "some record
        # somewhere satisfies this" and subject scope rested entirely on the
        # trusted export. A retracted record belonging to a different
        # subject proved the rule, with no axioms.
        L.append("  /-- whose case this is; every scoped binder checks it -/")
        L.append("  subject : String")
    for p in r["params"]:
        L.append(f"  /-- input `{p['name']}`: the key of the {p['type']} decided about -/")
        L.append(f"  {tb.camel(p['name'])} : String")
    if uses_as_of(r):
        # only when the rule asks for it, so a rule that says nothing about
        # time keeps the Snapshot it had and its artifacts do not churn
        L.append("  /-- the instant being decided, in whole days -/")
        L.append("  asOfDay : Int")
    L += ["deriving Repr", ""]
    # EVERY declared closure gets a definition. Emitting only the first
    # while a rule could name a second is how two hierarchies in one rule
    # failed to build at all.
    for clo in r["closures"]:
        cc = colls[clo["coll"]]
        ty = tb.pascal(cc["type"])
        fr, to = tb.camel(clo["from"]), tb.camel(clo["to"])
        fn = tb.camel(clo["name"])
        if cc["via"]:
            # A closure over a SCOPED collection walks only the scope's own
            # edges. The fold used to walk the whole list and rely on the
            # export to have scoped it, while the compiled search walked
            # every edge in the database: two samples sharing a pathway's
            # nodes then reached through each other's edges in the search,
            # the kernel rejected the witness, and the verdict was recorded
            # as a disagreement. Now both forms carry the scope.
            vf = tb.camel(cc["via"])
            L += [f"/-- closure `{clo['name']}` over `{clo['coll']}` (scoped to "
                  f"`{cc['scope'] or 'subject'}`), {clo['from']} → {clo['to']}: one round.",
                  "    Only unretracted edges belonging to the scope are walked. -/",
                  f"def {fn}Step (sc : String) (edges : List {ty}) (xs : List String) : List String :=",
                  f"  (xs ++ (edges.filter (fun e => e.retractedAt.isNone && "
                  f"e.{vf} == sc && xs.contains e.{fr})).map (·.{to})).eraseDups", "",
                  f"/-- `x` itself and everything it reaches within the scope. -/",
                  f"def {fn} (s : Snapshot) (x : String) : List String :=",
                  f"  (List.range (s.{clo['coll']}.length + 1)).foldl "
                  f"(fun xs _ => {fn}Step s.{scope_field(cc)} s.{clo['coll']} xs) [x]", ""]
            continue
        L += [f"/-- closure `{clo['name']}` over `{clo['coll']}`, {clo['from']} → {clo['to']}: "
              "one round.",
              "",
              "    A retracted edge is not walked. The TypeQL closure has",
              "    always guarded this (`active($e)` on every edge); the Lean",
              "    fold did not, because the guards were added to `some`",
              "    binders and closure collections were left out. The two",
              "    forms then asked different questions, and the dangerous",
              "    direction is a walking step inside `none of`: Lean reaches",
              "    the goal through a retracted edge, the block is false, the",
              "    kernel decides the negation, and the search also returns",
              "    nothing — so the per-case differential reports `agree` and",
              "    the verdict is recorded. -/",
              f"def {fn}Step (edges : List {ty}) (xs : List String) : List String :=",
              f"  (xs ++ (edges.filter (fun e => e.retractedAt.isNone && "
              f"xs.contains e.{fr})).map (·.{to})).eraseDups", "",
              f"/-- `x` itself and everything it reaches; `edges.length + 1` rounds reach the",
              f"    fixpoint on any finite graph, cycles included. -/",
              f"def {fn} (s : Snapshot) (x : String) : List String :=",
              f"  (List.range (s.{clo['coll']}.length + 1)).foldl "
              f"(fun xs _ => {fn}Step s.{clo['coll']} xs) [x]", ""]

    def cond(s):
        a, b = _side(r, model, s["lhs"]), _side(r, model, s["rhs"])

        def lean(x):
            if x[0] == "field":
                return f"{x[1]}.{x[3]}"
            if x[0] == "asof":
                return ("s.asOfDay" if x[1] == 0 else
                        f"(s.asOfDay {'-' if x[1] < 0 else '+'} {abs(x[1])})")
            # how a literal is written depends on the field it is compared
            # with: a constructor for an enum, a bare numeral for an Int, a
            # quoted string otherwise
            if a[0] == "field" and a[4] == "enum":
                # Lean compares a constructor and TypeQL the raw string, and
                # constructor names are mangled (`é`, `ü` → `_`), so a literal
                # that is not one of the declared values could mean one thing
                # to each form. Only a declared value is allowed.
                allowed = model["attributes"][a[2]]["values"] or []
                if x[1] not in allowed:
                    raise RuleError(
                        f"`{s['lhs']} {s['op']} {s['rhs']}`: {x[1]!r} is not "
                        f"one of the values of {a[2]!r}: {allowed}")
                return f".{tb.ctor(x[1])}"
            if a[0] == "field" and a[4] == "int":
                n = int(x[1])
                return f"({n})" if n < 0 else str(n)
            return tb.lean_str(x[1])

        if s["op"] not in COMPARISONS:
            # the step carries which closure it walks, resolved in `_check`;
            # neither compiler guesses
            return f"{lean(b)} ∈ {tb.camel(s['closure'])} s {lean(a)}"
        return f"{lean(a)} {LEAN_OP[s['op']]} {lean(b)}"

    def build(steps, i, depth):
        """One block as a Lean proposition.

        A `none of` block becomes `¬ (…)` around the same construction, so a
        negated condition is the ordinary one under a negation rather than a
        second code path that could disagree with it.
        """
        pad = "  " * (depth + 2)
        if i == len(steps):
            return "True"
        s = steps[i]
        rest = build(steps, i + 1, depth)
        if s["kind"] == "some":
            parts = binder_guards(s, colls)
            if rest != "True":
                parts.append(rest)
            body = f" ∧\n{pad}".join(parts) if parts else "True"
            return f"∃ {s['var']} ∈ s.{s['coll']},\n{pad}{body}"
        here = (f"¬ ({build(s['steps'], 0, depth + 1)})"
                if s["kind"] == "none" else cond(s))
        return here if rest == "True" else f"{here} ∧\n{pad}{rest}"

    L += [f"/-- {r['says']} -/",
          f"def {r['conclusion']} (s : Snapshot) : Prop :=",
          f"  {build(r['steps'], 0, 0)}", "",
          "-- Elaboration budget only. Putting the subject and the retraction",
          "-- check on every binder grew the proposition past the default",
          "-- instance-search size, and the search gave up on the largest",
          "-- rule. These three options raise limits; none of them affects",
          "-- what the kernel accepts, and `attest/rulec.py` emits no others",
          "-- (the core's own test suite checks that). A rule module is",
          "-- compared byte-for-byte with a fresh compile before every",
          "-- decision, so it cannot acquire an option the compiler did",
          "-- not write.",
          *SAFE_OPTIONS,
          f"instance (s : Snapshot) : Decidable ({r['conclusion']} s) := by",
          f"  unfold {r['conclusion']}; infer_instance", "",
          f"end {module(r, rules_namespace)}", ""]
    return "\n".join(L)


# ------------------------------------------------------------------ to TypeQL
def fn_names(r):
    # The whole id, so two rules of one family get two functions. The hash
    # alone would keep them apart, but a name that says only the family on
    # every search in it is unreadable in a schema dump.
    base = re.sub(r"[^A-Za-z0-9]+", "_", r["id"]).strip("_").lower()
    tag = r["sha"][:12]
    return (f"{base}_{tb.camel(r['conclusion']).lower()}_witness_{tag}",
            {c["name"]: f"{base}_{c['name'].replace('-', '_')}_{tag}" for c in r["closures"]})


def compile_typeql(r, model):
    """`define` block with the closure function(s) and the witness function."""
    _reject_role_vs_literal(r, model)
    _reject_bad_comparison(r, model)
    colls = {c["name"]: c for c in r["collections"]}
    wname, cnames = fn_names(r)
    out = ["define"]

    def active(v):
        return (f"{v} has recorded-at {v}_ra; {v}_ra <= $t; "
                f"not {{ {v} has retracted-at {v}_rx; {v}_rx <= $t; }};")

    for clo in r["closures"]:
        ety = colls[clo["coll"]]["type"]
        players = [n for n, t in model["types"].items()
                   if f"{ety}:{clo['from']}" in t["plays"]]
        if len(players) != 1:
            raise RuleError(f"closure {clo['name']}: expected one player type for "
                            f"{ety}:{clo['from']}, got {players}")
        pt = players[0]
        f = cnames[clo["name"]]
        cc = colls[clo["coll"]]
        if cc["via"]:
            # scoped: the walk is restricted to the scope's own edges, the
            # same restriction the Lean fold applies
            st = scope_type(r, cc)
            out += [f"fun {f}($x: {pt}, $sc: {st}, $t: datetime) -> {{ {pt} }}:",
                    "match",
                    f"  {{ $y isa {pt}; $y is $x; }} or",
                    f"  {{ let $m in {f}($x, $sc, $t);",
                    f"    $e isa {ety}, links ({clo['from']}: $m, {clo['to']}: $y, "
                    f"{cc['via']}: $sc); {active('$e')} }};",
                    "return { $y };", ""]
            continue
        out += [f"fun {f}($x: {pt}, $t: datetime) -> {{ {pt} }}:",
                "match",
                f"  {{ $y isa {pt}; $y is $x; }} or",
                f"  {{ let $m in {f}($x, $t);",
                f"    $e isa {ety}, links ({clo['from']}: $m, {clo['to']}: $y); {active('$e')} }};",
                "return { $y };", ""]

    subj = r["subject"]
    closures_by_name = {c["name"]: c for c in r["closures"]}
    body, bound_fields, rets = [], {}, []
    #: which statement list a variable's scope writes into. A field of an
    #: OUTER variable read inside `not { … }` has to be bound outside it, or
    #: the binding is local to the negation and the outer body never makes it.
    var_sink, k = {}, [0]

    def fvar(v, f, how):
        key = (v, f)
        if key not in bound_fields:
            name = f"${v}_{f.replace('-', '_')}"
            var_sink.get(v, body).append(
                f"  ${v} links ({f}: {name});" if how.startswith("role")
                else f"  ${v} has {f} {name};")
            bound_fields[key] = name
        return bound_fields[key]

    def emit(steps, sink, witness):
        """One block. `witness` is False inside a negation: an absence has no
        fact to cite, so its binders contribute nothing to the witness."""
        for s in steps:
            if s["kind"] == "none":
                inner = []
                emit(s["steps"], inner, False)
                sink.append("  not {")
                sink += ["  " + line for line in inner]
                sink.append("  };")
                continue
            if s["kind"] == "some":
                c = colls[s["coll"]]
                via = (f", links ({c['via']}: {scope_var(r, c)})"
                       if c["via"] else "")
                sink.append(f"  ${s['var']} isa {s['type']}{via}; "
                            f"{active('$' + s['var'])}")
                var_sink[s["var"]] = sink
                if witness:
                    sink.append(f"  ${s['var']} has fact-id ${s['var']}_fid;")
                    rets.append(f"${s['var']}_fid")
                continue
            a, b = _side(r, model, s["lhs"]), _side(r, model, s["rhs"])
            if s["op"] not in COMPARISONS:
                k[0] += 1
                xa = fvar(a[1], a[2], a[4])
                closure = cnames[s["closure"]]
                cc = colls[closures_by_name[s["closure"]]["coll"]]
                scope_arg = f"{scope_var(r, cc)}, " if cc["via"] else ""
                sink.append(f"  let $c{k[0]} in {closure}({xa}, {scope_arg}$t);")
                if b[0] == "lit":
                    # the group is named, so compare the reached entity's key
                    # — the same value Lean compares
                    key = role_key(r, model, a)
                    sink.append(f"  $c{k[0]} has {key} $k{k[0]};")
                    sink.append(f"  $k{k[0]} == {tb.tql_lit(b[1])};")
                else:
                    sink.append(f"  $c{k[0]} is "
                                f"{fvar(b[1], b[2], b[4])};")
            elif b[0] == "lit" and a[4].startswith("role"):
                # Lean compares the player's KEY, so TypeQL must too: the role
                # binds the entity, and comparing an entity to a string either
                # fails at `define` or quietly means something else.
                k[0] += 1
                key = role_key(r, model, a)
                x = fvar(a[1], a[2], a[4])
                sink.append(f"  {x} has {key} $k{k[0]};")
                sink.append(f"  $k{k[0]} {TQL_OP[s['op']]} {tb.tql_lit(b[1])};")
            elif b[0] == "asof":
                x = fvar(a[1], a[2], a[4])
                if b[1] == 0:
                    sink.append(f"  {x} {TQL_OP[s['op']]} $asof_day;")
                else:
                    # bound to a name rather than written inline, so the
                    # arithmetic is a `let` the server evaluates once
                    k[0] += 1
                    sign = "-" if b[1] < 0 else "+"
                    sink.append(f"  let $d{k[0]} = $asof_day {sign} "
                                f"{abs(b[1])};")
                    sink.append(f"  {x} {TQL_OP[s['op']]} $d{k[0]};")
            elif b[0] == "lit":
                x = fvar(a[1], a[2], a[4])
                lit = str(int(b[1])) if a[4] == "int" else tb.tql_lit(b[1])
                sink.append(f"  {x} {TQL_OP[s['op']]} {lit};")
            else:
                xa, xb = fvar(a[1], a[2], a[4]), fvar(b[1], b[2], b[4])
                if a[4].startswith("role"):
                    sink.append(f"  {xa} is {xb};" if s["op"] == "=" else
                                f"  not {{ {xa} is {xb}; }};")
                else:
                    sink.append(f"  {xa} {TQL_OP[s['op']]} {xb};")

    emit(r["steps"], body, True)
    # Every argument must be used, or TypeDB refuses the function
    # (`[FRP1] Function argument variable … is unused`). A rule whose
    # collections are all global — a check over reference data, say — never
    # mentioned `$subject` and so could not be deployed at all. Typing an
    # otherwise unused argument is a use, and constrains nothing the
    # caller did not already bind.
    if not any(c["via"] and (c["scope"] in (None, "subject"))
               for c in r["collections"]):
        body.insert(0, f"  $subject isa {subj};")
    for i, p in enumerate(r["params"]):
        body.insert(0, f"  $arg{i} isa {p['type']};")
    params = f"$subject: {subj}, " + "".join(
        f"$arg{i}: {p['type']}, " for i, p in enumerate(r["params"])) + "$t: datetime"
    if uses_as_of(r):
        params += ", $asof_day: integer"
    out += [f"fun {wname}({params}) -> "
            f"{{ {', '.join('fact-id' for _ in rets)} }}:",
            "match", *body,
            f"return {{ {', '.join(rets)} }};", ""]
    return "\n".join(out)


# ------------------------------------------- witness -> proof, relied facts
def witness_proof(r, model, snap_rows, fact_ids):
    """Proof term for `<Conclusion> snap` from the witness's fact-ids, in step
    order: each `some` contributes the record and its membership proof, each
    `require` a `by decide`. A `none of` block is one decidable proposition
    over the whole snapshot, so it contributes a single `by decide` and no
    record — there is no fact to cite for an absence. None if a fact is not
    in the snapshot."""
    colls = {c["name"]: c for c in r["collections"]}
    by_id = {}
    for c in r["collections"]:
        for row in snap_rows[c["name"]]:
            by_id[(c["name"], row["fact-id"])] = row
    parts, it = [], iter(fact_ids)
    for s in r["steps"]:
        if s["kind"] == "some":
            row = by_id.get((s["coll"], next(it)))
            if row is None:
                return None
            # the record, its membership proof, then one `by decide` for each
            # guard the binder carries (subject scope, non-retraction)
            parts += [tb.lean_literal(model, s["type"], row), "by decide"]
            parts += ["by decide"] * len(binder_guards(s, colls))
        else:
            parts.append("by decide")
    return "⟨" + ",\n   ".join(parts) + "⟩"


def double_negated_collections(r):
    """Collections a holding verdict depends on POSITIVELY from inside a
    negation: those bound (or walked) under an even number of `none of`,
    two or more deep.

    Polarity follows depth. Under one `none of` a fact can only make the
    block false, so retracting it can only make a holding verdict MORE
    true — nothing to flag. Under two it is the other way round: the
    "every condition is met" shape

        none of                      # no condition is missing ...
          some criterion c …
          none of                    # ... its resolution
            some resolution v …      # <- v supports the verdict

    holds because each `v` exists. Retract one and the inner block becomes
    true, the outer one false, and the verdict flips. The witness cites no
    `v` (there is none to cite: the proof of an absence names nothing), so
    impact analysis reported that retracting it affected no decision.
    """
    colls = {c["name"]: c for c in r["collections"]}
    closures = {c["name"]: c for c in r["closures"]}
    found = set()

    def walk(steps, depth):
        for s in steps:
            if s["kind"] == "none":
                walk(s["steps"], depth + 1)
            elif depth >= 2 and depth % 2 == 0:
                if s["kind"] == "some":
                    found.add(s["coll"])
                elif s["op"] not in COMPARISONS:
                    found.add(closures[s["closure"]]["coll"])
    walk(r["steps"], 0)
    return sorted(c for c in found if c in colls)


def relied_facts(r, model, snap_rows, fact_ids, scopes=None):
    """The witness's records; for each top-level walking step, the closure
    edges on its path; and every fact of a collection the verdict reads
    positively under a double negation (see `double_negated_collections`).

    `scopes` maps `subject` and each parameter to its key, so a path through
    a scoped closure is traced over the scope's own edges only, as both
    compiled forms walk it."""
    scopes = scopes or {}
    rows, it = {}, iter(fact_ids)
    for s in r["steps"]:
        if s["kind"] == "some":
            fid = next(it)
            rows[s["var"]] = next(x for x in snap_rows[s["coll"]] if x["fact-id"] == fid)
    facts = {row["fact-id"] for row in rows.values()}
    closures = {c["name"]: c for c in r["closures"]}
    colls = {c["name"]: c for c in r["collections"]}
    # top-level steps only: a walking step inside `none of` holds because no
    # path exists, so there are no edges to cite. What such a block does
    # depend on is everything that was *looked at* — which is the snapshot's
    # coverage, recorded separately from reliance.
    #
    # Paired by the step's OWN closure. Pairing every closure with every
    # step, as this did, cited the other hierarchy's edges as evidence for
    # a path they had nothing to do with — invisible while only one closure
    # could be declared.
    for s in r["steps"]:
        if s["kind"] == "require" and s["op"] not in COMPARISONS:
                clo = closures[s["closure"]]
                cc = colls[clo["coll"]]
                edges = [e for e in snap_rows[clo["coll"]]
                         if e.get("retracted-at") is None
                         and (not cc["via"]
                              or e.get(cc["via"]) == scopes.get(
                                  cc["scope"] or "subject"))]
                va, fa = s["lhs"].split(".", 1)
                start = rows[va][fa]
                # the right side is either another bound field or a NAMED
                # entity, in which case the name is itself the goal key
                if "." in s["rhs"]:
                    vb, fb = s["rhs"].split(".", 1)
                    goal = rows[vb][fb]
                else:
                    goal = s["rhs"].strip('"')
                prev, q = {start: None}, [start]
                while q:
                    x = q.pop(0)
                    for e in edges:
                        if e[clo["from"]] == x and e[clo["to"]] not in prev:
                            prev[e[clo["to"]]] = e
                            q.append(e[clo["to"]])
                x = goal
                while prev.get(x):
                    facts.add(prev[x]["fact-id"])
                    x = prev[x][clo["from"]]
    # Coarse but sound: every fact of a double-negated collection. Precise
    # would be "the facts that defeated each inner block", which needs an
    # evaluator of the rule outside Lean; over-citing costs only extra
    # flags in impact analysis, never a missed one.
    for name in double_negated_collections(r):
        facts.update(row["fact-id"] for row in snap_rows.get(name, [])
                     if row.get("fact-id") is not None)
    return sorted(facts)


# ------------------------------------------------------------------- shape
def shape(r):
    """A normalised structural fingerprint of the rule's obligation.

    The content hash of a rule answers "is this the same text". It cannot
    answer "is this the same QUESTION", and that is what a stored decision
    needs when a rule is edited. Why3 makes exactly this distinction and the
    difference is its most useful property: an MD5 for exact identity, and a
    *shape* for near identity, so a one-character change to a specification
    migrates the old proof attempts onto the new goal and marks them
    obsolete rather than orphaning them
    (Bobot et al., "Preserving User Proofs across Specification Changes").

    Attest had only the exact hash. Editing seven `latest` checks in one
    afternoon made every stored decision unrelatable to its successor, with
    nothing able to say "same obligation, re-check" rather than "different
    obligation, this history is gone".

    What the shape deliberately DROPS, because none of it changes the
    question being asked:

      the rule id and version · the `says` prose · comments and whitespace
      the author's variable names, renumbered in binding order
      the author's collection names, replaced by the type they range over

    What it KEEPS, because all of it does: the conclusion, the structure of
    binders and negations, every operator, every literal, every field, and
    which closure each walking step uses — itself shaped, not named.
    """
    colls = {c["name"]: c for c in r["collections"]}
    closures = {c["name"]: c for c in r["closures"]}

    def coll_shape(name):
        c = colls[name]
        # the scope is appended only when it is a parameter, so every rule
        # written before parameters existed keeps its shape hash
        sc = c.get("scope")
        return (f"{c['type']}/{c['via'] or '-'}"
                + (f"@{sc}" if sc not in (None, "subject") else ""))

    def clo_shape(name):
        c = closures[name]
        return f"{coll_shape(c['coll'])}:{c['from']}>{c['to']}"

    names: dict[str, str] = {}

    def side(expr):
        expr = expr.strip()
        if _AS_OF_RE.match(expr):
            m = _AS_OF_RE.match(expr)
            off = int(m.group(2) or 0) * (-1 if m.group(1) == "-" else 1)
            return f"asof{off:+d}" if off else "asof"
        if "." in expr:
            v, f = expr.split(".", 1)
            return f"{names.get(v, '?')}.{f}"
        return f"lit({expr.strip(chr(34))})"

    def walk(steps):
        out = []
        for s in steps:
            if s["kind"] == "some":
                names[s["var"]] = f"v{len(names)}"
                out.append(f"some({names[s['var']]}:{coll_shape(s['coll'])})")
            elif s["kind"] == "none":
                out.append("none[" + ",".join(walk(s["steps"])) + "]")
            else:
                op = (s["op"] if s["op"] in COMPARISONS
                      else f"walk<{clo_shape(s['closure'])}>")
                out.append(f"req({side(s['lhs'])}{op}{side(s['rhs'])})")
        return out

    body = ",".join(walk(r["steps"]))
    params = "".join(f"[{p['type']}]" for p in r.get("params", []))
    return f"{r['conclusion']}{params}({body})"


def shape_sha(r):
    """The shape's hash, for storing beside the exact rule hash."""
    return sha(shape(r))


def same_obligation(a, b) -> bool:
    """Whether two rules ask the same question, whatever their text."""
    return shape(a) == shape(b)


# ------------------------------------------------------------ sync & check
def segments(r):
    """The Lean module path for a rule id, one segment per dotted part.

    `billing.duplicate-claim` -> `['Billing', 'DuplicateClaim']`.

    The whole id is used, not just the first segment. A rule *family* — one
    rule per branch of a guideline or policy, all over the same schema — is
    the normal shape for anything with more than one outcome, and taking
    only the first segment made every member of a family compile to the same
    file: the last one written won, and the drift check then reported
    `Drift` on a rule nobody had touched.
    """
    return [tb.pascal(part) for part in r["id"].split(".")]




def module(r, rules_namespace):
    return ".".join([rules_namespace, *segments(r)])


def lean_path(r, lean_dir, rules_namespace):
    parts = segments(r)
    return os.path.join(lean_dir, *rules_namespace.split("."),
                        *parts[:-1], parts[-1] + ".lean")


def load(path):
    return parse(open(path).read())


def _norm(s):
    return re.sub(r"\s+", "", s)


def live_functions(schema_text):
    """Function blocks from TypeDB's schema text, by name."""
    blocks = re.split(r"(?=\bfun\s)", schema_text)
    return {re.match(r"fun\s+(\w+)", b).group(1): b.strip()
            for b in blocks if re.match(r"fun\s+\w+", b)}


class Drift(Exception):
    pass


def check(store, r, lean_dir, rules_namespace, schema_namespace, db=None):
    """Recompile `r` and require both deployed forms to equal the output.

    The Lean rule must be byte-identical and the deployed TypeQL function
    identical modulo whitespace, so the two can only differ if the compiler
    itself is wrong — which is what the per-case differential still watches.
    """
    database = db or store.database
    model = tb.parse(store.driver.databases.get(database).type_schema())
    path = lean_path(r, lean_dir, rules_namespace)
    want_lean = compile_lean(r, model, rules_namespace, schema_namespace)
    have_lean = open(path).read() if os.path.exists(path) else ""
    if have_lean != want_lean:
        raise Drift(f"{module(r, rules_namespace)} in use is not what rule "
                    f"{r['id']} (sha {r['sha'][:12]}) compiles to: recompile")
    want = live_functions(compile_typeql(r, model))
    have = live_functions(store.driver.databases.get(database).schema())
    for name, src in want.items():
        if name not in have:
            raise Drift(f"TypeDB has no function {name}: the deployed search is not "
                        f"rule {r['id']} sha {r['sha'][:12]}")
        if _norm(have[name]) != _norm(src):
            raise Drift(f"TypeDB function {name} differs from the compiled rule")
    return model
