import Mathlib.Tactic.Common
import Mathlib.Tactic.TacticAnalysis.Declarations

set_option linter.tacticAnalysis.tryAtEachStepAesop true

/-- info: `rfl` can be replaced with `aesop` -/
#guard_msgs in
theorem foo : 2 + 2 = 4 := by
  rfl
