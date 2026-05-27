import Extraction.Grind
import Extraction.Trace

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
-/
#guard_msgs(info, drop error) in
example : P 1 2 3 := by
  grind [p_eq_q] extract min_ast

/--
info: Try this:
  [apply] suffices «min_ast» : Q by grind [p_heq_q]
-/
#guard_msgs(info, drop error) in
example : P 1 2 3 := by
  grind [p_heq_q] extract min_ast

end NoFVars

variable (P : Nat → Nat → Nat → Prop) (Q : Prop) (h : P 1 2 3 = Q)

/--
info: Try this:
  [apply] suffices «min_ast» : Q by grind
-/
#guard_msgs(info, drop error) in
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
-/
#guard_msgs(info, drop error) in
example (h : ¬B 0 → B 0 = A) : B 0 := by
  grind extract min_ast

end ReasonForUsingSuffices

/--
info: Try this (`grind` succeeded, extraction is redundant):
  [apply] grind [=> id_def]
-/
#guard_msgs(info, drop error) in
example : true = !false := by
  grind [=> id_def] extract min_ast

/--
info: Try this:
  [apply] suffices «min_ast» : f b = 0 by grind
-/
#guard_msgs(info, drop error) in
example (f g : Nat → Nat) (h : g a = b) : f (g a) = 0 := by
  grind extract min_ast

/--
info: Try this:
  [apply] suffices «min_ast» : f b = 0 by grind
-/
#guard_msgs(info, drop error) in
example (f : Nat → Nat) (h : a = b) : f (a + 0) = 0 := by
  grind extract min_ast

/--
info: Try this:
  [apply] suffices «min_ast» : f 0 = 0 by grind
-/
#guard_msgs(info, drop error) in
example (f : Nat → Nat) (h : a + a = 0) : f (a + a) = 0 := by
  grind extract min_ast

/--
info: Try this:
  [apply] suffices «min_ast» : f 0 = 42 by grind
-/
#guard_msgs(info, drop error) in
example (f : Nat → Nat) (g : Nat → Nat → Nat) (h : g a a = 0) (h' : a = b) : f (g a b) = 42 := by
  grind extract min_ast

/--
info: Try this:
  [apply] suffices «ast_min» : 0 = 1 by grind
-/
#guard_msgs(info, drop error) in
example (h : a + a = 0) : a + a = 1 := by
  grind extract ast_min

-- **NOTE** This is an example where DFS-based extraction took a while. This is because the example
-- involves a cycle as a result of `f (x + y) = f (x + x) = f 0 = 0`. When traversing in DFS order,
-- we only discover that the smallest term equivalent to `f 0` is `0` after having reached
-- `f (f … (f 0))` and thereby running into the size limit.
/--
info: Try this:
  [apply] suffices «min_ast» : 0 = 1 by grind
-/
#guard_msgs(info, drop error) in
example (f : Nat → Nat) (h₁ : x = y) (h₂ : x + x = 0) (h₃ : f 0 = 0) : f (x + y) = 1 := by
  grind extract min_ast

variable (f : Nat → Nat) (x y : Nat)
variable (h₁ : x = y) (h₂ : x + x = 0) (h₃ : f 0 = 0)

set_option trace.grind.extract.minAST true

-- **TODO** We would have expected the e-class of `a + b` to contain `0` as well, but it doesn't.
--          Although, when just running `grind` and checking the diagnostics, the terms `0` and
--          `2 * a` are in the same equivalence class.
example (f : Nat → Nat) (h : a + a = 0) (h' : a = b) : f (a + b) = 42 := by
  grind extract min_ast

-- It seems that `grind` turns `a + a` into `2 * a` as part of preprocessing. As, for example, below
-- if we `set_option trace.grind.extract.minAST true`, we can see that extraction runs on
-- `2 * a = 1`, whereas in the theorem above, it runs on `f (a + b) = 42`. This causes problems
-- during extraction, as we will try to extract from `a + b` which does not show to be in the same
-- e-class as `2 * a`. Why not!?
example (h : a + a = 0) : a + a = 0 := by
  grind extract min_ast




variable (f : Nat → Nat) (a b : Nat)

-- **TODO** This should at least find the smaller term `f (a + a + a) = 0`.
example (f : Nat → Nat) (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) (h₄ : d = e)
    (h₅ : f a = 0) : f (a + (f b) + c + (f d) + e) = 0 := by
  grind -- extract min_ast
