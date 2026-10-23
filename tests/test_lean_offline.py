"""The generated Lean rules, checked by real Lean — no TypeDB server needed.

    PATH=<lean toolchain>/bin:$PATH python3 tests/test_lean_offline.py

For every fixture rule, on random snapshots (the golden ones that contain a
witness, plus some that may not), the kernel is asked to accept:

  * the verdict the reference evaluator (`tests/refeval.py`) predicts,
    proved `by decide` — so the Lean definition and an independent reading
    of the rule agree on what it means;
  * where there is a witness, the proof term `rulec.witness_proof` builds
    from it — so the proof builder produces terms the kernel accepts.

Case files are built with `runner.case_file`, the builder `decide` and
`recheck` share, so this also exercises the exact file format a decision
stores. Skips (exit 0) when `lake` is not on PATH.
"""

from __future__ import annotations

import datetime
import pathlib
import random
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

from attest import Kernel, rulec, runner  # noqa: E402
from attest.domain import LeanPackage  # noqa: E402
from golden import rules  # noqa: E402
import refeval  # noqa: E402
from refeval import random_case  # noqa: E402

#: random snapshots per rule beyond the golden witness cases
EXTRA = 3
#: as-of whose day number is the 20000 refeval assumes
AS_OF = (datetime.date(1970, 1, 1)
         + datetime.timedelta(days=20000)).isoformat() + "T00:00:00"


def main() -> int:
    if shutil.which("lake") is None:
        print("lake not on PATH: skipping the Lean checks")
        return 0
    import json
    golden = json.loads((HERE / "golden" / "compiler.json").read_text())
    failures, checks = [], 0
    built = set()
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="attest-lean-"))
    for label, rule, model, lean_dir, root in rules():
        if lean_dir not in built:
            done = subprocess.run(["lake", "build"], cwd=lean_dir,
                                  capture_output=True, text=True)
            if done.returncode != 0:
                failures.append(f"{lean_dir}: does not build\n"
                                f"{done.stdout[-400:]}{done.stderr[-400:]}")
                continue
            built.add(lean_dir)
        lean = LeanPackage(directory=lean_dir, root_module=root,
                           schema_namespace=f"{root}.Schema",
                           rules_namespace=f"{root}.Rules")
        kernel = Kernel(lean_dir, case_dir=tmp / root)
        # The golden cases are read as STORED SNAPSHOTS, not rebuilt from
        # their seeds. Rebuilding meant a change to how `refeval` draws
        # values silently changed which snapshots this suite checked, so the
        # golden file and this suite could drift apart while both passed.
        # The extra cases are still drawn fresh — they are there to roam, not
        # to be reproducible.
        cases = [("golden", i, c) for i, c in enumerate(golden[label]["cases"])]
        cases += [("fresh", 10_000 + i, None) for i in range(EXTRA)]
        for origin, seed, stored in cases:
            if stored is not None:
                case = refeval.Case(rule, model, stored["data"],
                                    stored["scopes"]["subject"],
                                    {k: v for k, v in stored["scopes"].items()
                                     if k != "subject"})
            else:
                case = random_case(rule, model, random.Random(seed), size=4)
            snapshot = runner.make_snapshot(
                case.scopes["subject"], AS_OF, case.data,
                params={k: v for k, v in case.scopes.items()
                        if k != "subject"})
            assert runner.as_of_day(AS_OF) == case.as_of_day
            cf = runner.case_file(snapshot, model, rule, lean)
            found = case.witnesses()
            statement = cf.positive if found else cf.negative
            result = cf.check(kernel, "agrees", statement, "by decide")
            checks += 1
            if not result.accepted:
                failures.append(f"{label} seed {seed}: Lean does not prove "
                                f"{statement!r}, which the reference "
                                f"evaluator predicts: {result.reason}")
            if found:
                term = rulec.witness_proof(rule, model, snapshot.data,
                                           list(found[0]))
                result = cf.check(kernel, "holds", cf.positive, term)
                checks += 1
                if not result.accepted:
                    failures.append(f"{label} seed {seed}: the witness proof "
                                    f"term is rejected: {result.reason}")
        print(f"  {label}: checked")
        if label.endswith("blocked.rule"):
            # A real timeout is reported as `not-run`, never as a rejection:
            # the decision procedure reads the two differently.
            impatient = Kernel(lean_dir, case_dir=tmp / "timeout",
                               timeout=0.001)
            impatient._built_at = impatient._fingerprint()
            result = cf.check(impatient, "late", cf.positive, "by decide")
            checks += 1
            if result.outcome != "not-run":
                failures.append(f"a timed-out check was reported as "
                                f"{result.outcome!r}: {result.reason}")
    for f in failures:
        print("  FAIL", f)
    print(f"{checks - len(failures)}/{checks} Lean checks passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
