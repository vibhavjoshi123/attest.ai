"""Attacks on the type bridge, each reproduced before it was fixed.

Every test here was a way to get the Lean kernel to accept a proof about data
that differs from what TypeDB holds or means, or to make the bridge write
outside its workspace. Found by four independent reviews that compared
`attest/typebridge.py` with lean-smt, lean-auto/LeanHammer and Z3's
`proof_to_lean.py`, and by attacking it directly.

Needs Lean on PATH (the string and constructor checks run the real kernel).
No TypeDB server.

    python3 tests/test_bridge.py
"""

from __future__ import annotations

import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from attest import rulec, typebridge as tb                           # noqa: E402
from attest.kernel import forbidden                                  # noqa: E402

PASS, FAIL = [], []


def check(name):
    def wrap(fn):
        try:
            fn()
            PASS.append(name)
        except Exception as exc:                                   # noqa: BLE001
            FAIL.append((name, f"{type(exc).__name__}: {exc}"))
        return fn
    return wrap


def raises(exc, fn, *a, contains=None):
    try:
        fn(*a)
    except exc as e:
        if contains and contains not in str(e):
            raise AssertionError(f"raised {exc.__name__} without {contains!r}: {e}")
        return e
    raise AssertionError(f"{fn.__name__} did not raise {exc.__name__}")


def lean(source: str) -> str:
    """Run Lean on `source`; return its output, raise if it reports an error."""
    d = tempfile.mkdtemp(prefix="bridge-test-")
    try:
        path = os.path.join(d, "T.lean")
        with open(path, "w") as f:
            f.write(source)
        out = subprocess.run(["lean", path], capture_output=True, text=True,
                             timeout=300)
        text = out.stdout + out.stderr
        if out.returncode != 0 or "error" in text:
            raise AssertionError("Lean rejected the file:\n" + text[-1500:])
        return text
    finally:
        shutil.rmtree(d, ignore_errors=True)


SCHEMA = """define
attribute name,
 value string;
attribute agent-code,
 value string;
attribute fact-id,
 value string;
entity person,
  owns name @key;
relation visit,
  relates who @card(1..1),
  relates agents,
  owns fact-id @key;
"""


# ------------------------------------------------------------ strings
@check("two different emoji are two different Lean strings (json.dumps made them both U+0000)")
def _():
    model = tb.parse(SCHEMA)
    a = tb.lean_literal(model, "person", {"name": "Dr 😀"})
    b = tb.lean_literal(model, "person", {"name": "Dr 😁"})
    out = lean("structure Person where\n  name : String\nderiving DecidableEq\n"
               f"theorem distinct : ({a} : Person) ≠ ({b} : Person) := by decide\n"
               "#print axioms distinct\n")
    assert "distinct" in out


STRINGS = ["", "plain", 'quote " in', "back\\slash", "new\nline", "tab\t",
           "cr\r", "bell\x07", "nul\x00", "bs\b ff\f", "del\x7f", "é ü ß",
           "日本語", "😀", "𠀀", "mixed 😀 \" \\ \n end", "-/ and /-", "«x»",
           "   ", "﻿bom"]


@check("every string round-trips through the Lean literal exactly, code point by code point")
def _():
    lines = []
    for i, s in enumerate(STRINGS):
        cps = ", ".join(str(ord(c)) for c in s)
        lines.append(f"example : ({tb.lean_str(s)}).toList.map Char.toNat = "
                     f"[{cps}] := by decide")
    lean("\n".join(lines) + "\n")


@check("a lone surrogate is refused, not written as U+0000")
def _():
    raises(ValueError, tb.lean_str, "\ud83d", contains="surrogate")


@check("TypeQL literals keep characters whole (no surrogate halves)")
def _():
    assert tb.tql_lit("😀") == '"😀"'
    assert tb.tql_lit('a"b') == '"a\\"b"'


# ------------------------------------------------------------ parser
@check("an escaped quote in @values is read as a quote, and two values that "
       "would share a constructor are refused")
def _():
    m = tb.parse('define\nattribute st,\n value string @values("a_b", "a\\"b");\n'
                 'entity e,\n  owns st @card(1..1);\n')
    assert m["attributes"]["st"]["values"] == ["a_b", 'a"b'], m["attributes"]["st"]
    raises(tb.UnsupportedSchema, tb._render, m, "0" * 64, "N",
           contains="distinct Lean constructors")


@check("non-ASCII enum values that mangle to one constructor are refused")
def _():
    m = tb.parse('define\nattribute st,\n value string @values("é", "ü");\n'
                 'entity e,\n  owns st @card(1..1);\n')
    raises(tb.UnsupportedSchema, tb._render, m, "0" * 64, "N")


@check("text inside an annotation cannot fake @key or @card")
def _():
    m = tb.parse('define\nattribute name,\n value string;\n'
                 'entity item,\n  owns name @values("@key", "@card(1..1)");\n')
    o = m["types"]["item"]["owns"][0]
    assert o["key"] is False and o["required"] is False, o
    assert tb.key_attr(m, "item") is None


@check("a `;` inside a quoted annotation does not split the statement")
def _():
    m = tb.parse('define\nattribute code,\n value string @regex("^[a-z;]+$");\n'
                 'attribute st,\n value string @values("x;y", "z");\n')
    assert m["attributes"]["st"]["values"] == ["x;y", "z"]


@check("unknown statements, clauses and annotations are refused, not skipped")
def _():
    for bad in ['define\nstruct point:\n x value integer;\n',
                'define\nrelation r,\n  relates a as b;\n',
                'define\nattribute n,\n value string;\nentity e,\n  owns n @cascade;\n']:
        raises(tb.UnsupportedSchema, tb.parse, bad)


@check("value types with no exact Lean mapping are refused, not turned into String")
def _():
    for vt in ("boolean", "double", "decimal", "date", "datetime-tz", "duration"):
        m = tb.parse(f'define\nattribute x,\n value {vt};\nentity e,\n  owns x;\n')
        raises(tb.UnsupportedSchema, tb.fields, m, "e", contains=vt)


@check("a multi-valued attribute is refused, not narrowed to one Option")
def _():
    for card in ("0..", "1..", "2..3"):
        raises(tb.UnsupportedSchema, tb.parse,
               f'define\nattribute x,\n value string;\nentity e,\n  owns x @card({card});\n')


@check("an attribute subtype keeps its parent's value type (was String)")
def _():
    m = tb.parse('define\nattribute amount @abstract,\n value integer;\n'
                 'attribute volume,\n sub amount;\nentity e,\n  owns volume @card(1..1);\n')
    assert tb.fields(m, "e") == [("volume", "volume", "Int", "int")], tb.fields(m, "e")


@check("a sub-relation keeps its parent's roles (they were dropped)")
def _():
    m = tb.parse('define\nrelation link @abstract,\n  relates from @card(1..1);\n'
                 'relation hop,\n  sub link,\n  relates to @card(1..1);\n')
    names = [f for (_, f, _, _) in tb.fields(m, "hop")]
    assert names == ["to", "from_"], names


# ------------------------------------------------------------ names
@check("two TypeDB names that become one Lean name are refused")
def _():
    m = tb.parse('define\nentity a-b,\n  owns n;\nentity a_b,\n  owns n;\n'
                 'attribute n,\n value string;\n')
    raises(tb.UnsupportedSchema, tb._render, m, "0" * 64, "N", contains="both become")
    m = tb.parse('define\nattribute x-y,\n value string;\nattribute x_y,\n value string;\n'
                 'entity e,\n  owns x-y,\n  owns x_y;\n')
    raises(tb.UnsupportedSchema, tb.fields, m, "e")


@check("a type that would shadow a prelude type (String, Int, ...) is refused")
def _():
    m = tb.parse('define\nattribute string,\n value string @values("a");\n'
                 'entity e,\n  owns string @card(1..1);\n')
    raises(tb.UnsupportedSchema, tb._render, m, "0" * 64, "N", contains="shadow")


@check("keywords and generated member names are escaped; leading digits made valid")
def _():
    assert tb.camel("return") == "return_" and tb.camel("rec") == "rec_"
    assert tb.ctor("1st") == "_1st" and tb.ctor("mk") == "mk_"
    raises(tb.UnsupportedSchema, tb.ctor, "")
    src = ("inductive K | " + " | ".join(tb.ctor(v) for v in
           ["1st", "mk", "rec", "for", "return", "calc", "elab"]) + "\n"
           "structure S where\n" + "".join(
               f"  {tb.camel(n)} : Nat\n" for n in
               ["return", "for", "calc", "rec", "mk", "sorry", "example"]))
    lean(src)


# ------------------------------------------------------------ rows
@check("a bare string for a list role is refused (it was split into characters)")
def _():
    m = tb.parse(SCHEMA)
    raises(ValueError, tb.lean_literal, m, "visit",
           {"who": "p1", "agents": "agent-x", "fact-id": "v1"}, contains="list")


@check("unknown and missing row keys are refused, not ignored or defaulted")
def _():
    m = tb.parse(SCHEMA)
    raises(ValueError, tb.lean_literal, m, "visit",
           {"who": "p1", "agents": [], "fact-id": "v1", "agnets": ["x"]},
           contains="does not have")
    raises(ValueError, tb.lean_literal, m, "visit", {"who": "p1", "fact-id": "v1"},
           contains="lacks")


@check("a non-string value for a string field is refused (True was sent as \"True\")")
def _():
    m = tb.parse(SCHEMA)
    raises(ValueError, tb.lean_literal, m, "person", {"name": True})


# ------------------------------------------------------------ sync and artifacts
class _DB:
    def __init__(self, types, functions=""):
        self.t, self.f = types, functions

    def type_schema(self):
        return self.t

    def schema(self):
        return self.t + self.f


class _Store:
    database = "db"

    def __init__(self, db, rows=None):
        self._db, self._rows = db, rows or []
        self.driver = type("D", (), {"databases": type("Ds", (), {
            "get": staticmethod(lambda name: db)})()})()

    def rows(self, query, tx=None):
        return self._rows


@check("check_sync refuses a Schema.lean whose body was edited but whose hash line was kept")
def _():
    store = _Store(_DB(SCHEMA))
    d = tempfile.mkdtemp()
    try:
        path = os.path.join(d, "Schema.lean")
        tb.generate(store, path, "N")
        src = open(path).read()
        tb.check_sync(_Store(_DB(SCHEMA), rows=[{"a": 1}]), path, [], "N")
        forged = src.replace("end N", "instance : OfNat Int 65 := ⟨50⟩\nend N")
        open(path, "w").write(forged)
        raises(tb.OutOfSync, tb.check_sync, store, path, [], "N",
               contains="hash line matches")
    finally:
        shutil.rmtree(d, ignore_errors=True)


@check("materialize refuses a module name that would write outside the workspace")
def _():
    d = tempfile.mkdtemp()
    outside = os.path.join(d, "OUTSIDE")
    try:
        work = os.path.join(d, "ws")
        lean_dir = os.path.join(d, "pkg")
        os.makedirs(lean_dir)
        open(os.path.join(lean_dir, "lakefile.lean"), "w").write("")
        src = "-- forged\n"
        # a path segment that starts with "/" resets os.path.join to an
        # absolute path, so the old code wrote this exact file
        assert "." not in outside, outside
        row = {"m": "X." + os.path.join(outside, "pwned"), "s": src,
               "k": "theorems", "h": tb.sha(src)}
        raises(tb.OutOfSync, tb.materialize, _Store(None, rows=[row]),
               ["x@1"], lean_dir, "Root", work)
        assert not os.path.exists(outside), "a file was written outside the workspace"
    finally:
        shutil.rmtree(d, ignore_errors=True)


# ------------------------------------------------------------ compiler and kernel
@check("a rule may only compare an enum field with one of its declared values")
def _():
    schema = ('define\nattribute fact-id,\n value string;\n'
              'attribute grade,\n value string @values("strong", "weak");\n'
              'entity holder,\n  owns fact-id @key,\n  plays holding:holder;\n'
              'relation holding,\n  relates holder @card(1..1),\n'
              '  owns fact-id @key,\n  owns grade @card(1..1);\n')
    model = tb.parse(schema)
    good = rulec.parse('rule demo.g v0.1\nsays "x"\nsubject holder\n'
                       'collection hs : holding for subject via holder\n'
                       'conclude G when\n  some holding a in hs\n'
                       '  require a.grade = strong\n')
    rulec.compile_lean(good, model, "R", "N")
    bad = rulec.parse(good["source"].replace("= strong", "= strông"))
    raises(rulec.RuleError, rulec.compile_lean, bad, model, "R", "N", contains="not one of")


@check("a quoted name spelling a forbidden command is data; the command itself is still refused")
def _():
    assert forbidden('def x := K.«elab»\ndef y := "set_option"\n') is None
    assert forbidden("set_option debug.skipKernelTC true\n") == "set_option"


if __name__ == "__main__":
    for name in PASS:
        print(f"  pass  {name}")
    for name, why in FAIL:
        print(f"  FAIL  {name}\n          {why}")
    print(f"\n{len(PASS)}/{len(PASS) + len(FAIL)} passed")
    sys.exit(1 if FAIL else 0)
