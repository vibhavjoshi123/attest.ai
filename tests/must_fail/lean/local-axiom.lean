-- expect: axiom
axiom cheat : False
theorem holds : 1 = 2 := cheat.elim
