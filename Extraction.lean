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

section FVars

/--
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ Q
-/
#guard_msgs in
example (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 = Q) : P 1 2 3 := by
  grind extract min_ast

/--
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ Q
-/
#guard_msgs in
example (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 = Q) : P 1 2 3 := by
  grind extract Q

/--
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 = Q) : P 1 2 3 := by
  grind extract P 1 2 3

/--
error: unsolved goals
P : Nat → Nat → Nat → Prop
Q : Prop
h : P 1 2 3 = Q
⊢ P 1 2 3
-/
#guard_msgs in
example (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 = Q) : Q := by
  grind extract P _ _ _

-- TODO: Why does this not work? Logging in `extractExpr?` indicates that while we do traverse the
--       entire e-class, the `isDefEq` check simply always fails. Is this because we don't
--       translate mvars into grind's context?
example (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 = Q) : Q := by
  grind extract _

end FVars
