/-
  GENERATED from the live TypeDB schema by attest/typebridge.py.
  Do not edit: change the schema and regenerate.
  schema sha256 (types + functions): 8052ba149a1cc433d996847ef23863e90c9b007043ffb1dbed750753b47a2d3c
-/
namespace Sanctions.Schema

def schemaSha256 : String := "8052ba149a1cc433d996847ef23863e90c9b007043ffb1dbed750753b47a2d3c"

/-- TypeDB `attribute decided-by` @values -/
inductive DecidedBy | witness | negation | evaluation
deriving DecidableEq, Repr

/-- TypeDB `attribute list-status` @values -/
inductive ListStatus | active | delisted
deriving DecidableEq, Repr

/-- TypeDB `entity artifact` -/
structure Artifact where
  artifactId : String
  artifactKind : String
  leanModule : String
  leanSource : String
  recordedAt : String
  sourceSha256 : String
deriving DecidableEq, Repr

/-- TypeDB `relation coverage` -/
structure Coverage where
  decision : String
  item : String
deriving DecidableEq, Repr

/-- TypeDB `relation decision` -/
structure Decision where
  subject : String
  asOf : String
  certificateHash : String
  decidedAt : String
  decidedBy : DecidedBy
  decisionId : String
  decisionInputs : Option String
  ruleShape : String
  ruleVersion : String
  snapshotHash : String
  verdict : String
deriving DecidableEq, Repr

/-- TypeDB `relation engagement` (sub fact) -/
structure Engagement where
  vendor : String
  contractRef : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

/-- TypeDB `relation governance` -/
structure Governance where
  artifact : String
  decision : String
deriving DecidableEq, Repr

/-- TypeDB `entity ledger` -/
structure Ledger where
  highWater : String
  ledgerId : String
deriving DecidableEq, Repr

/-- TypeDB `relation listing` (sub fact) -/
structure Listing where
  party : String
  factId : String
  listStatus : ListStatus
  recordedAt : String
  regime : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

/-- TypeDB `relation ownership` (sub fact) -/
structure Ownership where
  owned : String
  owner : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

/-- TypeDB `entity party` (sub subject) -/
structure Party where
  lei : String
deriving DecidableEq, Repr

/-- TypeDB `entity proof` -/
structure Proof where
  axiomsUsed : String
  kernelVersion : String
  proofId : String
  proofSource : String
  proofTerm : String
  statement : String
  theoremName : String
deriving DecidableEq, Repr

/-- TypeDB `relation proved-by` -/
structure ProvedBy where
  decision : String
  proof : String
deriving DecidableEq, Repr

/-- TypeDB `relation reliance` -/
structure Reliance where
  decision : String
  evidence : String
deriving DecidableEq, Repr

end Sanctions.Schema
