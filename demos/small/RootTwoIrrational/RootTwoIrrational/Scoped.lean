import Mathlib

/-!
# Scoped declarations

Exercises the scoping machinery end to end: namespaces (nested),
sections, and `variable` binders. The demo workflow verifies these
targets against the real API on every run, so scope handling is
exercised live.
-/

namespace Scoped

variable (n : Nat)

/-- A theorem whose statement depends on a section variable. -/
theorem variable_holds : n = n := rfl

namespace Deep

/-- A theorem inside a nested namespace. -/
theorem deep_holds : 1 + 1 = 2 := rfl

end Deep

section Helpers

variable (m : Nat)

/-- A theorem under two variable declarations and a section. -/
theorem helpers_holds : m = m := rfl

end Helpers

end Scoped
