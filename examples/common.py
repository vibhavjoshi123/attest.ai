"""Helpers shared by the examples. Nothing here is trusted: it only reads.

Every export follows the same three rules the core asks of a domain:

* one read transaction for the whole snapshot;
* every lookup goes through `Store.lookup`, which refuses if a fact lacking a
  required attribute was silently dropped;
* rows are keyed by TypeDB names (roles, attributes, `fact-id`) so the
  compiled rule can turn them into Lean values with no adapter.
"""
from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from attest.store import as_of, dt, ident  # noqa: E402


def stamp(value) -> str:
    """A datetime as the driver returns it, in the ISO form the ledger uses."""
    text = str(value).replace(" ", "T").replace("Z", "").split("+")[0]
    return text.rstrip("0").rstrip(".") if "." in text else text


def facts(store, tx, var: str, pattern: str, roles: dict[str, str],
          attrs: dict[str, str], t: str) -> list[dict]:
    """Every fact matching `pattern` that stands at `t`, one row each.

    `roles` maps a role name to the variable bound to its player's key;
    `attrs` maps an attribute name to the variable bound to its value.
    `retracted-at` is deliberately `None`: as of `t` the fact stands, and
    copying a LATER retraction into the row would change the snapshot's hash
    after the fact and break replay.
    """
    tag = var.lstrip("$")
    cols = {"fact-id": f"$fid_{tag}", "source": f"$src_{tag}",
            "recorded-at": f"$ra_{tag}", **roles, **attrs}
    base = f"{pattern} {as_of(var, t)}"
    extra = (f"{var} has fact-id $fid_{tag}, has source $src_{tag};"
             + "".join(f" {var} has {a} {v};" for a, v in attrs.items()))
    rows = store.lookup(tx, base, extra, ", ".join(cols.values()), var)
    out = []
    for row in rows:
        rec = {name: row[v.lstrip("$")] for name, v in cols.items()}
        rec["recorded-at"] = stamp(rec["recorded-at"])
        rec["retracted-at"] = None
        out.append(rec)
    return sorted(out, key=lambda r: r["fact-id"])


__all__ = ["ROOT", "facts", "stamp", "dt", "ident"]
