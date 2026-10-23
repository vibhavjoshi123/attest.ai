/-
  GENERATED from the live TypeDB schema by attest/typebridge.py.
  Do not edit: change the schema and regenerate.
  schema sha256 (types + functions): 950c6e81dab6ae9891f4fcedefa4fee76f03753aaf24e922025c24570e2495fb
-/
namespace Fixture.Schema

def schemaSha256 : String := "950c6e81dab6ae9891f4fcedefa4fee76f03753aaf24e922025c24570e2495fb"

/-- TypeDB `attribute decided-by` @values -/
inductive DecidedBy | witness | negation | evaluation
deriving DecidableEq, Repr

/-- TypeDB `attribute state` @values -/
inductive State | met | unmet | unknown
deriving DecidableEq, Repr

/-- TypeDB `attribute status` @values -/
inductive Status | active | lifted
deriving DecidableEq, Repr

/-- TypeDB `attribute test-code` @values -/
inductive TestCode | alpha | beta
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

/-- TypeDB `relation claim` (sub fact) -/
structure Claim where
  code : String
  holder : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

/-- TypeDB `entity code` -/
structure Code where
  codeKey : String
deriving DecidableEq, Repr

/-- TypeDB `relation code-isa` (sub fact) -/
structure CodeIsa where
  child : String
  parent : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

/-- TypeDB `relation coverage` -/
structure Coverage where
  decision : String
  item : String
deriving DecidableEq, Repr

/-- TypeDB `relation criterion` (sub fact) -/
structure Criterion where
  item : String
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

/-- TypeDB `relation engagement` (sub fact) -/
structure Engagement where
  counterparty : String
  holder : String
  factId : String
  recordedAt : String
  ref : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

/-- TypeDB `entity firm` (sub party) -/
structure Firm where
  partyKey : String
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

/-- TypeDB `entity holder` (sub subject) -/
structure Holder where
  holderId : String
deriving DecidableEq, Repr

/-- TypeDB `entity item` -/
structure Item where
  itemKey : String
deriving DecidableEq, Repr

/-- TypeDB `relation item-mark` (sub fact) -/
structure ItemMark where
  item : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
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
  recordedAt : String
  retractedAt : Option String
  source : String
  status : Status
deriving DecidableEq, Repr

/-- TypeDB `entity node` -/
structure Node where
  nodeKey : String
deriving DecidableEq, Repr

/-- TypeDB `relation open-edge` (sub fact) -/
structure OpenEdge where
  holder : String
  origin : String
  target : String
  factId : String
  recordedAt : String
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

/-- TypeDB `entity party` -/
structure Party where
  partyKey : String
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

/-- TypeDB `relation reading` (sub fact) -/
structure Reading where
  holder : String
  amount : Int
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
  takenDay : Int
  testCode : TestCode
deriving DecidableEq, Repr

/-- TypeDB `relation reliance` -/
structure Reliance where
  decision : String
  evidence : String
deriving DecidableEq, Repr

/-- TypeDB `relation resolution` (sub fact) -/
structure Resolution where
  holder : String
  critKey : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
  state : State
deriving DecidableEq, Repr

/-- TypeDB `relation start-node` (sub fact) -/
structure StartNode where
  holder : String
  node : String
  factId : String
  recordedAt : String
  retractedAt : Option String
  source : String
deriving DecidableEq, Repr

end Fixture.Schema
