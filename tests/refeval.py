"""The reference evaluator, kept importable from its original name.

The code moved to `attest/search/world.py`, where every searcher can reach
it: the counterexample search, the property prover and the abduction CLI all
need the same generator and the same reference reading of a rule, and a
module under `tests/` is not importable from `attest/`.

This re-export exists so the move is not also a rename for the five test
modules that already import `refeval`, and so the pinned generator outputs
keep comparing the same function.
"""

from attest.search.world import (          # noqa: F401
    AS_OF_RE,
    Case,
    add,
    drop,
    random_case,
)

__all__ = ["AS_OF_RE", "Case", "add", "drop", "random_case"]
