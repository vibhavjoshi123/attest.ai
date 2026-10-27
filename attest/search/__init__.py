"""Untrusted search around the kernel. Nothing here decides anything.

Every searcher in this package proposes; the kernel in `attest/kernel.py`
disposes. A searcher may be as clever, as statistical or as wrong as it
likes, because its output is a candidate that the core re-checks — the same
asymmetry that lets TypeDB's search be untrusted.

Two rules hold this apart from the core, and both are tested rather than
merely stated:

* **The core never imports this package.** `attest/__init__.py` does not
  export `search`, and a test parses every module under `attest/` outside
  this directory and fails on any import of `attest.search`.
* **No co-residence.** The process that runs `decide`, `record` or
  `recheck` does not import this package at all. Each tool here runs as its
  own `python -I -m attest.search.<tool>` and exchanges JSON, because
  untrusted code sharing a process with `decide` could rebind
  `kernel.STANDARD_AXIOMS` or `Kernel.check` at runtime, which no static
  import check would catch.

`world.py` is the shared snapshot generator and the reference reading of a
rule. It is the one module here the tests also use, which is why it was
promoted out of `tests/`.
"""

__all__: list[str] = []
