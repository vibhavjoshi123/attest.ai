-- expect: implemented_by
@[implemented_by id] def f (n : Nat) : Nat := n
theorem holds : f 1 = 1 := rfl
