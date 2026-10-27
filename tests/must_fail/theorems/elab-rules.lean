-- expect: elab_rules
elab_rules : term | `(cheat) => return .const ``True []
theorem t : 1 = 1 := rfl
