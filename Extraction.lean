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
theorem t : P 1 2 3 := by
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

/--
info: Try this:
  [apply] suffices «Q» : Q by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract Q

/--
info: Try this:
  [apply] suffices «P 1 2 3» : P 1 2 3 by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract P 1 2 3

/--
info: Try this:
  [apply] suffices «P _ _ _» : P 1 2 3 by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ Q
-/
#guard_msgs in
example : Q := by
  grind extract P _ _ _

section ReasonForUsingSuffices

opaque A : Prop
opaque B : Prop

-- We use `suffices` for "proof construction", as if we used `have` or direct proof replacement, we
-- couldn't handle cases where the proof of equality between the goal and the extracted term depends
-- on the negation of the goal.
/--
info: Try this:
  [apply] suffices «A» : A by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h✝ : P 1 2 3 = Q
h : ¬B → B = A
⊢ B
-/
#guard_msgs in
example (h : ¬B → B = A) : B := by
  grind extract A

end ReasonForUsingSuffices

-- BUG: Term has not been internalized.
example (f : Nat → Nat) (a b : Nat) (h : a = b) : f (a + 0) = 0 := by
  grind extract min_ast

-- BUG: isDefEq fails on all comparisons to _ (that is, ?m.12345)
example : P 1 2 3 := by
  grind extract _
