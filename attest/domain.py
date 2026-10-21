"""What a domain has to supply, and nothing more.

The division is the whole point of the package. The core owns everything that
must not vary; a domain owns only what is genuinely domain knowledge:

    schema_path   what facts exist
    rule_path     the rule, written once
    lean          where its Lean package lives
    snapshot()    how to read one case out of the store
    scope()       what that read looked at

Note what is **not** in that list any more. The search, the proof term, the
facts a verdict relied on, and the Lean definition of the rule are all
*compiled from the rule file* by :mod:`attest.rulec`, and the Lean types are
generated from the live schema by :mod:`attest.typebridge`. A domain that
hand-wrote a TypeQL search and a Lean rule could have them disagree, and the
only thing that would notice is a case where they happen to differ. Compiled
from one source, they cannot.

What a domain still writes is therefore: the facts, the rule in a language a
domain expert can read, and the export that turns a subject into a snapshot.
"""

from __future__ import annotations

import pathlib
from dataclasses import dataclass, field
from typing import Any, Protocol


@dataclass(frozen=True)
class LeanPackage:
    """A Lake package, and the namespaces the compiler writes into."""

    directory: pathlib.Path
    #: the module importing everything, e.g. "Acme"
    root_module: str
    #: where generated types go, e.g. "Acme.Schema"
    schema_namespace: str
    #: where compiled rules go, e.g. "Acme.Rules"
    rules_namespace: str
    #: hand-written modules — theorems proved *about* the generated rule
    theorem_modules: tuple[str, ...] = ()

    @property
    def schema_path(self) -> pathlib.Path:
        return (self.directory.joinpath(*self.schema_namespace.split("."))
                .with_suffix(".lean"))

    def module_path(self, module: str) -> pathlib.Path:
        return self.directory.joinpath(*module.split(".")).with_suffix(".lean")


@dataclass(frozen=True)
class Snapshot:
    """The facts a decision saw, and the hash that lets it be replayed.

    `data` is keyed by the rule's collection names, and each row is keyed by
    **TypeDB** names — roles, attributes, and `fact-id`. That is what lets the
    compiled rule build a Lean value and a proof term from it without an
    adapter per domain.
    """

    subject: str
    as_of: str
    data: dict[str, list[dict[str, Any]]]
    sha256: str
    fact_ids: tuple[str, ...] = ()
    #: (type, key-attribute, value) triples naming the items the export looked
    #: at, written as `coverage` edges
    scope: tuple[tuple[str, str, str], ...] = field(default_factory=tuple)
    #: anything the export defaulted rather than read, named in the certificate
    assumptions: tuple[str, ...] = field(default_factory=tuple)


class Domain(Protocol):
    """One rule over one schema. A domain implements this and nothing else."""

    schema_path: pathlib.Path
    rule_path: pathlib.Path
    lean: LeanPackage
    #: the entity a decision is about, and the attribute that identifies it
    subject_type: str
    subject_key: str

    def subjects(self, store: Any, as_of: str) -> list[str]:
        """Every subject with facts to decide about.

        For callers that sweep a population; the core decides one subject at
        a time and never calls this.
        """
        ...

    def snapshot(self, store: Any, subject: str, as_of: str) -> Snapshot:
        """Read the facts. Trusted, so keep the queries simple and
        non-recursive — the recursion belongs in the compiled search, whose
        answers are re-checked."""
        ...

    #: Patterns binding `$d` through a `coverage` edge, used by
    #: :func:`attest.affected_decisions` to find decisions broken by a fact
    #: ADDED after they were taken. `{fid}` is substituted with the fact id.
    #:
    #: This is required, not optional. The core cannot know which role of
    #: which relation makes a fact "about" a covered item, and a domain that
    #: supplies none gets only the retraction half of impact analysis — so a
    #: later fact silently leaves every earlier decision looking valid.
    #: Declare `scope_anchors = ()` to say that absence is deliberate.
    scope_anchors: tuple[str, ...]

    def scope(self, snapshot: Snapshot) -> list[tuple[str, str, str]]:
        """The items this export *looked at*, whether or not it found
        anything about them.

        The facts a verdict used find decisions broken by a RETRACTION. This
        finds those broken by an **addition** — a fact recorded later that
        the snapshot would have read had it existed.

        Called by :func:`attest.make_snapshot` callers to fill
        `Snapshot.scope`; the core reads the snapshot, so an export that
        populates `scope` directly may return it unchanged.
        """
        ...
