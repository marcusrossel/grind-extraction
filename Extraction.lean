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

section MVarTranslation

-- We need to translate mvars from the outer context to grind's context, as otherwise an outer mvar
-- `m` does not unify with expressions from the inner context containing fvars, as `m` has a
-- different local context.
/--
info: Try this:
  [apply] suffices «_» : P 1 2 3 by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract _

end MVarTranslation

/--
warning: `grind` succeeded, extraction is redundant
---
info: Try this:
  [apply] grind [=> id_def]
-/
#guard_msgs in
example : true = !false := by
  grind [=> id_def] extract _

/--
info: Try this:
  [apply] suffices «_ |ₛ _» : P 1 2 3 by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract _ |ₛ _

/--
info: Try this:
  [apply] suffices «Q |ₛ _» : Q by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract Q |ₛ _

/--
info: Try this:
  [apply] suffices «_ |ₛ Q» : P 1 2 3 by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract _ |ₛ Q

/--
info: Try this:
  [apply] suffices «P 1 2 3 |ₛ Q» : P 1 2 3 by grind
---
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example : P 1 2 3 := by
  grind extract P 1 2 3 |ₛ Q

-- BUG: Term has not been internalized.
example (f : Nat → Nat) (a b : Nat) (h : a = b) : f (a + 0) = 0 := by
  grind extract min_ast
