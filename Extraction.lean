-- This module serves as the root of the `Extraction` library.
-- Import modules here that should be built as part of the library.
import Extraction.Basic

inductive P : Nat → Nat → Nat → Prop
  | intro : P 1 2 3

inductive Q : Prop
  | intro

section NoFVars

theorem p_eq_q : P 1 2 3 = Q := by
  simp [P.intro, Q.intro]

theorem p_heq_q : P 1 2 3 ≍ Q := by
  simp [P.intro, Q.intro]

/--
error: unsolved goals
⊢ Q
-/
#guard_msgs in
example : P 1 2 3 := by
  grind [p_eq_q] extract min_ast

/--
error: unsolved goals
⊢ Q
-/
#guard_msgs in
example : P 1 2 3 := by
  grind [p_heq_q] extract min_ast

end NoFVars

/-- error: (kernel) declaration has free variables '_example' -/
#guard_msgs in
example (h : P 1 2 3 ↔ Q) : P 1 2 3 := by
  grind extract min_ast
  constructor
