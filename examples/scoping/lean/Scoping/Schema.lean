/-
  GENERATED from the live TypeDB schema by attest/typebridge.py.
  Do not edit: change the schema and regenerate.
  schema sha256 (types + functions): d9d856199187ac453b0e768e8a9883b015b0477edd3fd67ecbf7af65ed262455
-/
namespace Scoping.Schema

def schemaSha256 : String := "d9d856199187ac453b0e768e8a9883b015b0477edd3fd67ecbf7af65ed262455"

/-- TypeDB `attribute decided-by` @values -/
inductive DecidedBy | witness | negation | evaluation
deriving DecidableEq, Repr

/-- TypeDB `attribute state` @values -/
inductive State | resolved_true | resolved_false | unknown
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

/-- TypeDB `relation criterion` (sub fact) -/
structure Criterion where
  edge : String
  critKey : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
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

/-- TypeDB `entity edge-def` -/
structure EdgeDef where
  edgeId : String
deriving DecidableEq, Repr

/-- TypeDB `relation edge-mark` (sub fact) -/
structure EdgeMark where
  edge : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

/-- TypeDB `relation goal-mark` (sub fact) -/
structure GoalMark where
  node : String
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

/-- TypeDB `entity node` -/
structure Node where
  nodeId : String
deriving DecidableEq, Repr

/-- TypeDB `relation open-edge` (sub fact) -/
structure OpenEdge where
  origin : String
  sample : String
  target : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
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

/-- TypeDB `relation resolution` (sub fact) -/
structure Resolution where
  sample : String
  critKey : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
  state : State
deriving DecidableEq, Repr

/-- TypeDB `entity sample` (sub subject) -/
structure Sample where
  sampleId : String
deriving DecidableEq, Repr

/-- TypeDB `relation start-node` (sub fact) -/
structure StartNode where
  node : String
  sample : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

end Scoping.Schema
