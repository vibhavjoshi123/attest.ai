"""Attest: a verification layer. Search proposes, the Lean kernel decides.

This package is the whole core. A domain lives outside it, implementing
:class:`~attest.domain.Domain` — a schema, a rule file, and an export.
Nothing here knows what any domain is about.
"""

from . import rulec, typebridge
from .config import StoreConfig
from .domain import Domain, LeanPackage, Snapshot
from .kernel import STANDARD_AXIOMS, Check, Kernel
from .rulec import Drift, RuleError
from .runner import (
    decisions_after_rule_change,
    Certificate,
    affected_decisions,
    decide,
    decisions_relying_on,
        govern,
    hash_json,
    sync,
    verdicts,
    lean_snapshot,
    make_snapshot,
    Recheck,
    publish,
    recheck,
    record,
    search,
    sha256,
    sources_of,
    tql_str,
)
from .store import (
    CORE_SCHEMA,
    Ingest,
    SnapshotIncomplete,
    ConcurrentWrite,
    Store,
    UnknownSubject,
    VerificationError,
    as_of,
    dt,
    ident,
)
from .typebridge import OutOfSync

__all__ = [
    "CORE_SCHEMA", "STANDARD_AXIOMS",
    "Certificate", "Check", "ConcurrentWrite", "Domain", "Drift", "Ingest", "Kernel",
    "LeanPackage", "OutOfSync", "RuleError", "Snapshot", "SnapshotIncomplete",
    "Recheck", "Store", "StoreConfig", "UnknownSubject", "VerificationError",
    "affected_decisions", "as_of", "decide", "decisions_relying_on",
    "dt", "govern", "hash_json", "ident",
    "lean_snapshot", "make_snapshot", "publish", "record", "rulec", "search",
    "decisions_after_rule_change", "recheck", "sha256", "sources_of", "sync", "tql_str", "typebridge", "verdicts",
]
