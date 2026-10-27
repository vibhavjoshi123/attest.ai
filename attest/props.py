"""Declared properties: what a release claims about a whole rule set.

A rule says what one branch means. A property says something about *every*
snapshot of several branches at once — that two of them never both apply,
that one implies another, that a trap row cannot change a verdict. Those
claims are what lets a release say "these branches never co-occur" rather
than "no case we tried broke it".

This module holds the declaration and its parser, and nothing else yet. It
is in the core and not in `attest/search/` for the same reason
`rulec.compile_lean` is: a property's *statement* is whatever generates it,
so a model may never write one. The statement generators
(`derive`, `family_module`, `challenge_module`) arrive with the property
prover; what is here is the part the counterexample search needs first,
which is the declaration itself.

Declarations live in a sidecar `.family` file next to the rules, parsed
here rather than by `rulec.parse`, so the rule language and its golden
files are untouched:

    family fixture.alpha-band over alpha
      says "the two band branches never both apply, and a
            future-dated result never changes either"
      exclusive: latest-high, latest-low
      stable-add: latest-high, latest-low for readings when taken-day > as-of-day
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Literal


class FamilyError(Exception):
    """A `.family` file that cannot be read as declarations."""


#: what a declaration can claim. `exclusive`, `covers` and `implies` are
#: about one snapshot; the `stable-*` kinds are about a CHANGE to one, which
#: is why they alone carry `collections` and `when`.
KINDS = ("exclusive", "covers", "implies", "stable-add", "stable-retract")
_CHANGE_KINDS = ("stable-add", "stable-retract")

_ID = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*(\.[A-Za-z_][A-Za-z0-9_-]*)*$")
_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*$")
_KIND_LINE = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*\s*:")


@dataclass(frozen=True)
class PropertyDecl:
    """One claim, as a human declared and signed it.

    Shared with the counterexample search, which reads it through
    `attest.search.cx.props_eval.predicate` to decide whether a set of
    verdicts violates it. Nothing here is generated: every field comes from
    the `.family` text, so a reviewer can read the file and know what the
    release is claiming.
    """

    id: str
    kind: Literal["exclusive", "covers", "implies",
                  "stable-add", "stable-retract"]
    rules: tuple[str, ...]
    #: a rule whose holding is the precondition — "among accounts that are
    #: open, exactly one of these applies". Without it the claim is
    #: about every snapshot.
    gate: str | None = None
    #: `stable-*` only: the collections a row may be added to or retracted
    #: from
    collections: tuple[str, ...] = ()
    #: `stable-*` only: which rows, in the rule language's `require` syntax
    when: str | None = None
    says: str = ""

    def __post_init__(self) -> None:
        if self.kind not in KINDS:
            raise FamilyError(
                f"{self.id}: unknown kind {self.kind!r}; one of "
                f"{', '.join(KINDS)}")
        if not _ID.match(self.id):
            raise FamilyError(f"{self.id!r} is not a property id")
        if len(self.rules) < _MIN_RULES[self.kind]:
            raise FamilyError(
                f"{self.id}: {self.kind} needs at least "
                f"{_MIN_RULES[self.kind]} rule(s), got {len(self.rules)}")
        if len(set(self.rules)) != len(self.rules):
            raise FamilyError(f"{self.id}: a rule is named twice")
        for name in (*self.rules, *self.collections):
            if not _NAME.match(name):
                raise FamilyError(f"{self.id}: {name!r} is not a name")
        if self.gate is not None and not _NAME.match(self.gate):
            raise FamilyError(f"{self.id}: gate {self.gate!r} is not a name")
        if self.kind in _CHANGE_KINDS:
            if not self.collections:
                raise FamilyError(
                    f"{self.id}: {self.kind} needs `for <collection>`, "
                    f"or it does not say what may change")
        elif self.collections or self.when:
            raise FamilyError(
                f"{self.id}: {self.kind} is about one snapshot, so it takes "
                f"no `for` or `when` clause")


#: `implies` relates two rules in order; the rest need at least two to be
#: saying anything, except `covers`, which can claim a single rule always
#: holds under its gate
_MIN_RULES = {"exclusive": 2, "covers": 1, "implies": 2,
              "stable-add": 1, "stable-retract": 1}


def _rules(text: str, where: str) -> tuple[str, ...]:
    out = tuple(r.strip() for r in text.split(",") if r.strip())
    if not out:
        raise FamilyError(f"{where}: no rules named")
    return out


def parse_family(text: str) -> list[PropertyDecl]:
    """Every declaration in a `.family` file.

    One `family` block can carry several claims; each `<kind>:` line
    becomes its own `PropertyDecl`, taking the block's id, gate and `says`.
    The ids are suffixed with the kind, so `family fixture.alpha-band` with
    an `exclusive` and a `stable-add` line gives
    `fixture.alpha-band.exclusive` and `fixture.alpha-band.stable-add`.
    """
    out: list[PropertyDecl] = []
    fid: str | None = None
    gate: str | None = None
    says: list[str] = []
    seen: set[str] = set()
    pending: list[tuple[int, str, str]] = []

    def flush() -> None:
        prose = " ".join(" ".join(says).split())
        for line_no, kind, rest in pending:
            try:
                out.append(_declaration(fid, gate, prose, kind, rest))
            except FamilyError as exc:
                raise FamilyError(f"line {line_no}: {exc}") from None
        pending.clear()
        says.clear()

    for line_no, raw in enumerate(text.splitlines(), 1):
        line = raw.split("#", 1)[0].rstrip()
        if not line.strip():
            continue
        head = line.split()[0]
        if head == "family":
            flush()
            words = line.split()
            if len(words) == 2:
                fid, gate = words[1], None
            elif len(words) == 4 and words[2] == "over":
                fid, gate = words[1], words[3]
            else:
                raise FamilyError(
                    f"line {line_no}: expected `family <id> [over <rule>]`")
            if fid in seen:
                raise FamilyError(f"line {line_no}: family {fid} declared twice")
            seen.add(fid)
        elif head == "says":
            if fid is None:
                raise FamilyError(f"line {line_no}: `says` before any `family`")
            says.append(line.strip()[len("says"):].strip().strip('"'))
        elif _KIND_LINE.match(line.strip()):
            # Anything shaped `<word>:` is a declaration ATTEMPT. Deciding
            # that first is what keeps a misspelled kind from being read as
            # more `says` prose: `excluded: a, b` used to be swallowed into
            # the sentence above it, and the file was then refused for
            # having no declarations at all — a confusing report of a
            # typo three lines earlier.
            kind, rest = line.split(":", 1)
            kind = kind.strip()
            if kind not in KINDS:
                raise FamilyError(
                    f"line {line_no}: unknown kind {kind!r}; one of "
                    f"{', '.join(KINDS)}")
            if fid is None:
                raise FamilyError(
                    f"line {line_no}: `{kind}` before any `family`")
            pending.append((line_no, kind, rest.strip()))
        elif says and raw[:1].isspace():
            says.append(line.strip().strip('"'))      # a continued `says`
        else:
            raise FamilyError(f"line {line_no}: unknown line {head!r}")
    flush()
    if not out:
        raise FamilyError("no declarations: a .family file needs one")
    return out


def _declaration(fid, gate, says, kind, rest) -> PropertyDecl:
    collections: tuple[str, ...] = ()
    when: str | None = None
    if kind in _CHANGE_KINDS:
        body, _, filt = rest.partition(" when ")
        rules_text, sep, colls = body.partition(" for ")
        if not sep:
            raise FamilyError(
                f"{kind} needs `for <collection>[, ...]`, or it does not say "
                f"what may change")
        collections = _rules(colls, kind)
        when = filt.strip() or None
        rest = rules_text
    elif " for " in rest or " when " in rest:
        # Refused before the clause is mistaken for part of a rule name,
        # which reported `'b for readings' is not a name` and said nothing
        # about the real mistake.
        raise FamilyError(
            f"{kind} is about one snapshot, so it takes no `for` or `when` "
            f"clause")
    return PropertyDecl(
        id=f"{fid}.{kind}", kind=kind, rules=_rules(rest, kind),
        gate=gate, collections=collections, when=when, says=says)


def validate(decls, known: set[str]) -> None:
    """Every rule and gate a declaration names must exist.

    A declaration names rules by their short name, and nothing in the file
    itself can tell whether they are real. Without this the mistake
    surfaces much later and much worse: `predicate` asks for the verdict of
    a rule nobody can decide, raises, and the search never runs.

    This is not hypothetical. A natural first draft declares
    `family fixture.alpha-band over alpha`, and the fixture has no `alpha`
    rule — `alpha` is a test-code VALUE inside the rules. The claim it
    describes is in fact ungated, which is what
    `Fixture/Properties.lean:band_exclusive` already proves: for all
    readings, with only fact-id uniqueness assumed.
    """
    for decl in decls:
        unknown = [r for r in decl.rules if r not in known]
        if unknown:
            raise FamilyError(
                f"{decl.id} names {', '.join(sorted(unknown))}, which "
                f"{'is' if len(unknown) == 1 else 'are'} not among the "
                f"rules it is declared over ({', '.join(sorted(known))})")
        if decl.gate is not None and decl.gate not in known:
            raise FamilyError(
                f"{decl.id}: the gate {decl.gate!r} is not a rule. A gate "
                f"is a rule whose holding is the precondition, not a value "
                f"a rule compares against")
