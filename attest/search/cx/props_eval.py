"""Reading a declaration on verdicts, in microseconds.

The counterexample search needs to ask "do these verdicts violate the
claim?" millions of times, so it asks the reference evaluator rather than
the kernel: `world.Case.witnesses` gives each rule's verdict directly, and
this turns a `PropertyDecl` into a function over those verdicts.

**This is untrusted and it is not the property.** What the property *says*
is whatever `attest/props.py` generates as a Lean statement, and only the
kernel decides whether it holds. This module exists to find candidates
cheaply; every candidate it flags is then confirmed by the kernel, and a
disagreement between the two readings is itself a defect to report (the
cross-check in PLAN §4.1). Keeping the fast reading here, outside the core,
is what makes that cross-check meaningful: two implementations that shared
code would agree for the wrong reason.
"""

from __future__ import annotations

from typing import Callable

from attest.props import KINDS, PropertyDecl

#: a reading takes the verdicts of one snapshot and, for the `stable-*`
#: kinds, the verdicts after the change. `None` means "no change made".
Verdicts = dict
Reading = Callable[[Verdicts, "Verdicts | None"], bool]


def predicate(decl: PropertyDecl) -> Reading:
    """`decl` as a function returning True when the claim HOLDS.

    The search looks for a `False`. Each reading needs every rule the
    declaration names to have a verdict; a missing one is a bug in the
    caller rather than a violation, so it raises instead of returning
    False — a silent False would be reported as a counterexample and waste
    a kernel confirmation on nothing.
    """
    if decl.kind not in KINDS:                       # pragma: no cover
        raise ValueError(f"unknown kind {decl.kind!r}")

    def need(verdicts: Verdicts, which) -> list[bool]:
        missing = [r for r in which if r not in verdicts]
        if missing:
            raise KeyError(
                f"{decl.id}: no verdict for {', '.join(missing)}; the "
                f"caller must decide every rule the declaration names")
        return [bool(verdicts[r]) for r in which]

    def gated(verdicts: Verdicts) -> bool:
        """Is the precondition in force? Without a gate, always."""
        if decl.gate is None:
            return True
        return bool(need(verdicts, (decl.gate,))[0])

    if decl.kind == "exclusive":
        def holds(verdicts, after=None):
            if not gated(verdicts):
                return True
            return sum(need(verdicts, decl.rules)) <= 1
    elif decl.kind == "covers":
        def holds(verdicts, after=None):
            if not gated(verdicts):
                return True
            return any(need(verdicts, decl.rules))
    elif decl.kind == "implies":
        def holds(verdicts, after=None):
            if not gated(verdicts):
                return True
            # `implies: a, b, c` reads as a -> b and a -> c: the first rule
            # is the antecedent. Pairwise chaining would be a different
            # claim, and a weaker one.
            first, *rest = need(verdicts, decl.rules)
            return (not first) or all(rest)
    else:                                            # stable-add, stable-retract
        def holds(verdicts, after=None):
            if after is None:
                raise ValueError(
                    f"{decl.id}: {decl.kind} is about a change, so it needs "
                    f"the verdicts after it as well")
            if not gated(verdicts):
                return True
            before = need(verdicts, decl.rules)
            return before == need(after, decl.rules)

    holds.__name__ = f"holds_{decl.kind.replace('-', '_')}"
    holds.__doc__ = f"{decl.id}: {decl.says or decl.kind}"
    return holds
