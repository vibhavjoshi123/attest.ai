"""The sanctions-screening use cases, end to end on live TypeDB + Lean.

Four cases on one unchanged core: a party blocked through a two-step
ownership chain, one whose owner's listing was delisted, a correction that
retracts an ownership record, and an owner listed after a decision was made.
Each case asserts its verdict and its impact-analysis hits, so a run that
reaches the wrong answer exits non-zero rather than printing it.

Every value in the trace comes from the real call: hashes, witnesses, the
kernel's verdicts and axioms, the facts a verdict relied on, and the
impact-analysis hits. The clock is scripted, so two runs write the same
trace byte for byte; `scripts/examples.sh` runs it twice and compares.

    python3 examples/sanctions/run.py      # needs TypeDB 3 and Lean on PATH
"""
from __future__ import annotations

import datetime
import json
import pathlib
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent), str(HERE.parents[1])]

from attest import rulec, runner  # noqa: E402
from attest.kernel import Kernel  # noqa: E402
from attest.store import Ingest, Store  # noqa: E402
from domain import Sanctions, SanctionsIngest  # noqa: E402

TRACE: list[dict] = []




class Clock:
    """A scripted clock. Fixed times, only ever moving forward.

    Wall-clock time made this run unreproducible, and not harmlessly: the
    as-of time is part of the snapshot hash, so every run rewrote every hash
    in the trace, and a trace that never comes back the same cannot be
    checked against anything.
    """

    START = "2026-10-01T00:00:00"

    def __init__(self) -> None:
        self.at = datetime.datetime.fromisoformat(self.START)

    def __call__(self) -> str:
        return self.at.strftime("%Y-%m-%dT%H:%M:%S")

    def tick(self, seconds: int = 60) -> str:
        """Advance and return the new time: an as-of strictly after every
        write so far, and still comfortably in the past."""
        self.at += datetime.timedelta(seconds=seconds)
        return self()


CLOCK = Clock()

#: Decision ids are fresh uuids, so they cannot be reproduced. The trace
#: gets a stable label instead, in order of creation; the real id is printed
#: but not committed, since nothing is verified against it.
LABELS: dict[str, str] = {}
#: label -> the real id, for the code that has to pass one back to the core
REAL: dict[str, str] = {}


def label(did: str) -> str:
    """A stable name for a decision, for the trace."""
    if did not in LABELS:
        LABELS[did] = f"decision-{len(LABELS) + 1}"
        REAL[LABELS[did]] = did
    return LABELS[did]


def settle() -> str:
    """An as-of time strictly after every write so far, and not in the future."""
    return CLOCK.tick()

FAILURES: list[str] = []


def expect(condition: bool, what: str) -> None:
    """A use case's expected outcome. Every one is checked, and the run
    exits non-zero if any did not hold."""
    if not condition:
        FAILURES.append(what)
        print(f"  EXPECTATION FAILED: {what}")


class UseCase:
    def __init__(self, key, title, domain, story):
        self.d = {"key": key, "title": title, "domain": domain,
                  "story": story, "steps": [], "outcome": None}
        TRACE.append(self.d)

    def step(self, src, dst, msg, kind="call"):
        self.d["steps"].append({"from": src, "to": dst, "msg": msg,
                                "kind": kind})

    def note(self, text):
        self.d["steps"].append({"kind": "note", "msg": text})

    def outcome(self, text, verdict=None):
        self.d["outcome"] = {"text": text, "verdict": verdict}
        print(f"[{self.d['key']}] {text}")


def short(h, n=10):
    return h[:n]


def traced_decide(uc, store, domain, kernel, subject, as_of, *, record=True):
    rule = rulec.load(domain.rule_path)
    uc.step("Caller", "runner", f"decide {subject} as of {as_of[11:19]}")
    uc.step("runner", "compiler",
            f"recompile {rule['id']}, compare Lean file + TypeQL fun + schema hash")
    started = time.time()
    cert = runner.decide(store, domain, subject, as_of, kernel=kernel)
    elapsed = time.time() - started
    uc.step("compiler", "runner", "no drift", "reply")
    snap = cert.snapshot
    counts = ", ".join(f"{k} {len(v)}" for k, v in snap.data.items())
    uc.step("runner", "TypeDB", f"export snapshot as of {as_of[11:19]} (one read tx)")
    uc.step("TypeDB", "runner", f"{counts} · sha {short(snap.sha256)}", "reply")
    uc.step("runner", "TypeDB", "call compiled witness function")
    if cert.witnesses:
        uc.step("TypeDB", "runner",
                "witness " + ", ".join(sorted(cert.witnesses)[0]), "reply")
    else:
        uc.step("TypeDB", "runner", "nothing found (not trusted)", "reply")
    for a in cert.accepted + cert.rejected:
        how = ("proof term built from witness" if a["name"] == "holds"
               else "by decide")
        uc.step("runner", "Lean", f"theorem {a['statement']} := {how}")
        if a["accepted"]:
            uc.step("Lean", "runner",
                    f"ACCEPTED · axioms [{', '.join(a['axioms'])}]", "reply")
        else:
            uc.step("Lean", "runner", f"rejected: {a['reason'][:60]}", "error")
    # `elapsed` measures this machine, not a claim anyone verifies, so it is
    # printed and not traced — it was the other thing rewriting the trace on
    # every run.
    result = {"verdict": cert.verdict, "snapshot": snap.sha256,
              "witnesses": cert.witnesses, "relied_on": cert.relied_on,
              "differential": cert.differential,
              "scope": [s[2] for s in snap.scope], "decision": None}
    if record and cert.settled:
        did = runner.record(store, cert, domain.subject_type,
                            domain.subject_key, CLOCK())
        runner.govern(store, did, cert.artifacts)
        result["decision"] = label(did)
        uc.step("runner", "TypeDB",
                f"record {label(did)}: proof + reliance {len(cert.relied_on)}"
                f" + coverage {len(snap.scope)} + governance (one tx)")
        print(f"       {label(did)} = {did}  ({elapsed:.1f}s)")
    uc.note(f"verdict {cert.verdict} · differential {cert.differential}")
    return cert, result


def traced_refusal(uc, src, dst, msg, fn, scrub=None):
    uc.step(src, dst, msg)
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        text = f"{type(exc).__name__}: {str(exc).splitlines()[0]}"
        if scrub is not None:
            text = scrub(text)
        uc.step(dst, src, text[:110], "error")
        return text
    uc.step(dst, src, "NOT refused", "error")
    return None


def impact(uc, store, domain, fid):
    uc.step("Ingest", "runner", f"affected_decisions({fid})")
    hits = runner.affected_decisions(store, fid, domain.scope_anchors)
    if hits:
        for h in hits:
            uc.step("TypeDB", "runner",
                    f"{label(h['did'])} (was {h['v']}): {h['why']}", "reply")
    else:
        uc.step("TypeDB", "runner", "no decisions affected", "reply")
    return hits


# ────────────────────────────────────────────────────── sanctions
def sanctions_cases():
    dom = Sanctions()
    store = Store("ex_sanctions")
    store.reset(dom.schema_path)
    runner.sync(store, dom)
    runner.publish(store, dom, CLOCK())
    kernel = Kernel(dom.lean.directory)
    store.write(" ".join(
        f'insert $x{i} isa party, has lei "{p}";'
        for i, p in enumerate(["V-ACME", "HOLDCO", "LISTED-X",
                               "V-CLEAN", "PARENT-Y"])))
    ing = Ingest(store, clock=CLOCK)
    s = SanctionsIngest(ing)
    s.engage("eg-1", "V-ACME", "C-100", "procurement:2026-q4")
    s.owns("ow-1", "V-ACME", "HOLDCO", "registry:uk")
    s.owns("ow-2", "HOLDCO", "LISTED-X", "registry:cy")
    s.list("ls-1", "LISTED-X", "OFAC-SDN", "active", "list:ofac")
    s.engage("eg-2", "V-CLEAN", "C-200", "procurement:2026-q4")
    s.owns("ow-3", "V-CLEAN", "PARENT-Y", "registry:de")
    s.list("ls-2", "PARENT-Y", "EU", "delisted", "list:eu")
    t1 = settle()

    uc = UseCase("S1", "Blocked through a two-step ownership chain", "sanctions",
                 "V-ACME is owned by HOLDCO, which is owned by LISTED-X, "
                 "which has an active OFAC listing.")
    c1, r1 = traced_decide(uc, store, dom, kernel, "V-ACME", t1)
    uc.d["result"] = r1
    uc.outcome(f"{c1.verdict}: relied on {', '.join(c1.relied_on)} "
               f"(both ownership hops)", c1.verdict)
    expect(c1.verdict == "Blocked", f"S1 verdict {c1.verdict}, want Blocked")
    expect({"ow-1", "ow-2", "ls-1"} <= set(c1.relied_on),
           f"S1 relied on {c1.relied_on}, want both hops and the listing")

    uc = UseCase("S2", "Owner was listed, but the listing is delisted", "sanctions",
                 "V-CLEAN is owned by PARENT-Y, whose EU listing is delisted.")
    c2, r2 = traced_decide(uc, store, dom, kernel, "V-CLEAN", t1)
    uc.d["result"] = r2
    uc.outcome(f"{c2.verdict}: Lean proved no active listing is reachable",
               c2.verdict)
    expect(c2.verdict == "not Blocked", f"S2 verdict {c2.verdict}, "
                                        f"want not Blocked")

    uc = UseCase("S3", "Correction: an ownership record was wrong", "sanctions",
                 "The registry entry HOLDCO owned by LISTED-X (ow-2) is retracted.")
    uc.step("Caller", "Ingest", "retract ow-2")
    stamp = ing.retract("ow-2")
    uc.step("Ingest", "TypeDB", f"ow-2 has retracted-at {stamp[11:23]} (ledger CAS)")
    hits = impact(uc, store, dom, "ow-2")
    t2 = settle()
    c3, r3 = traced_decide(uc, store, dom, kernel, "V-ACME", t2)
    uc.d["result"] = {**r3, "affected": [label(h["did"]) for h in hits]}
    uc.outcome(f"impact found {len(hits)} decision(s); re-decided {c3.verdict}",
               c3.verdict)
    expect(len(hits) == 1, f"S3 impact found {len(hits)} decisions, want 1")
    expect(c3.verdict == "not Blocked", f"S3 verdict {c3.verdict}, "
                                        f"want not Blocked")

    uc = UseCase("S4", "Addition: the owner is newly listed", "sanctions",
                 "PARENT-Y gets a new, active UK listing after S2 was decided.")
    uc.step("Caller", "Ingest", "list ls-3: PARENT-Y UK-HMT active")
    s.list("ls-3", "PARENT-Y", "UK-HMT", "active", "list:uk")
    uc.step("Ingest", "TypeDB", "insert ls-3 with recorded-at (ledger CAS)")
    hits = impact(uc, store, dom, "ls-3")
    t3 = settle()
    c4, r4 = traced_decide(uc, store, dom, kernel, "V-CLEAN", t3)
    uc.d["result"] = {**r4, "affected": [label(h["did"]) for h in hits]}
    uc.outcome(f"coverage found {len(hits)} earlier decision(s); "
               f"re-decided {c4.verdict}", c4.verdict)
    expect(len(hits) == 1, f"S4 coverage found {len(hits)} decisions, want 1")
    expect(c4.verdict == "Blocked", f"S4 verdict {c4.verdict}, want Blocked")
    store.close()



if __name__ == "__main__":
    sanctions_cases()
    out = HERE / "trace.json"
    out.write_text(json.dumps(TRACE, indent=2) + "\n")
    print(f"\ntrace: {out}")
    if FAILURES:
        print(f"{len(FAILURES)} expectation(s) failed")
        sys.exit(1)
    print("all expectations held")
