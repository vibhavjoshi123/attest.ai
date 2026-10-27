-- expect: macro_rules
macro_rules | `(tactic| trivially) => `(tactic| rfl)
theorem t : 1 = 1 := rfl
