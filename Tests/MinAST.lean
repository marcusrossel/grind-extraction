import Extraction.Grind

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
info: Try this:
  [apply] suffices «min_ast» : Q by grind [p_eq_q]
---
error: unsolved goals
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind [p_eq_q] extract min_ast

/--
info: Try this:
  [apply] suffices «min_ast» : Q by grind [p_heq_q]
---
error: unsolved goals
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind [p_heq_q] extract min_ast

end NoFVars

variable (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 = Q)

/--
info: Try this:
  [apply] suffices «min_ast» : Q by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract min_ast

section ReasonForUsingSuffices

opaque A : Prop
opaque B : Nat → Prop

-- We use `suffices` for "proof construction", as if we used `have` or direct proof replacement, we
-- couldn't handle cases where the proof of equality between the goal and the extracted term depends
-- on the negation of the goal. By using `suffices`, we instead add the missing assumption *into*
-- grind's context.
/--
info: Try this:
  [apply] suffices «min_ast» : A by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h✝ : P 1 2 3 = Q
h : ¬B 0 → B 0 = A
⊢ B 0
-/
#guard_msgs in
example (h : ¬B 0 → B 0 = A) : B 0 := by
  grind extract min_ast

end ReasonForUsingSuffices

/--
warning: `grind` succeeded, extraction is redundant
---
info: Try this:
  [apply] grind [=> id_def]
-/
#guard_msgs in
example : true = !false := by
  grind [=> id_def] extract min_ast

/--
info: Try this:
  [apply] suffices «min_ast» : f b = 0 by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h✝ : P 1 2 3 = Q
f g : Nat → Nat
a b : Nat
h : g a = b
⊢ f (g a) = 0
-/
#guard_msgs in
example (f g : Nat → Nat) (a b : Nat) (h : g a = b) : f (g a) = 0 := by
  grind extract min_ast

-- BUG: Term has not been internalized.
example (f : Nat → Nat) (a b : Nat) (h : a = b) : f (a + 0) = 0 := by
  grind extract min_ast
