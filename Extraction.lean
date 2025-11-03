-- This module serves as the root of the `Extraction` library.
-- Import modules here that should be built as part of the library.
import Extraction.Basic

section NoFVars

inductive P : Nat → Nat → Nat → Prop
  | intro : P 1 2 3

inductive Q : Prop
  | intro

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

-- PROBLEM: The proof term contains fvars from grind's local context. That is, we're managing to get
--          terms *into* grind, but not out of it. How does grind handle the latter?
example (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 ↔ Q) : P 1 2 3 := by
  grind extract min_ast
  constructor
