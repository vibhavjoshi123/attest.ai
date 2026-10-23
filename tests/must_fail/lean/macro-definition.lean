-- expect: macro
macro "trust_me" : tactic => `(tactic| sorry)
theorem holds : 1 = 2 := by trust_me
