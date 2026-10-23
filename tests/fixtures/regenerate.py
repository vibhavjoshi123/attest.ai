"""Write the fixture's Lean package: what `sync` would generate for it.

    python3 tests/fixtures/regenerate.py

The package in `tests/fixtures/lean/` is generated, never hand-edited: the
Lean types from `schema.tql` (through `tests/schema_offline.py`, standing in
for a live server) and one module per rule in `rules/` from the compiler.
`tests/golden.py` then holds the compiler to these committed files byte for
byte, so a change to what the compiler emits shows up as a diff here that
has to be reviewed and regenerated deliberately.

The schema hash in `Schema.lean` is the hash of the canonical schema text,
in place of the hash of a live server's schema. Nothing compares it with a
server; it only has to be stable.
"""

from __future__ import annotations

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE.parent))

from attest import rulec, typebridge  # noqa: E402
import schema_offline  # noqa: E402

LEAN = HERE / "lean"
ROOT_MODULE = "Fixture"
SCHEMA_NS = f"{ROOT_MODULE}.Schema"
RULES_NS = f"{ROOT_MODULE}.Rules"
TOOLCHAIN = "leanprover/lean4:v4.35.0\n"


def rules():
    return [rulec.load(p) for p in sorted((HERE / "rules").glob("*.rule"))]


def main() -> int:
    text = schema_offline.canonical(HERE / "schema.tql")
    model = typebridge.parse(text)
    schema_lean = typebridge._render(model, typebridge.sha(text), SCHEMA_NS)

    (LEAN / ROOT_MODULE).mkdir(parents=True, exist_ok=True)
    (LEAN / "lean-toolchain").write_text(TOOLCHAIN)
    (LEAN / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\n\npackage fixture\n\n"
        f"@[default_target]\nlean_lib {ROOT_MODULE}\n")
    (LEAN / ROOT_MODULE / "Schema.lean").write_text(schema_lean)

    modules = [SCHEMA_NS]
    for rule in rules():
        path = pathlib.Path(rulec.lean_path(rule, str(LEAN), RULES_NS))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rulec.compile_lean(rule, model, RULES_NS, SCHEMA_NS))
        modules.append(rulec.module(rule, RULES_NS))
    (LEAN / f"{ROOT_MODULE}.lean").write_text(
        "".join(f"import {m}\n" for m in modules))
    print(f"wrote {len(modules) - 1} rule modules and the types to "
          f"{LEAN.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
