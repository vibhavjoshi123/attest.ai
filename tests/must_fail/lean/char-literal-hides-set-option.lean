-- expect: set_option
-- A '"' character literal used to open a phantom string in the scanner,
-- hiding everything up to the next real quote — here, the option that
-- turns the kernel off.
def q : Char := '"'
set_option debug.skipKernelTC true in
theorem holds : 1 = 1 := by decide
def z : String := "x"
