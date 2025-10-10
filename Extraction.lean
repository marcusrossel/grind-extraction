-- This module serves as the root of the `Extraction` library.
-- Import modules here that should be built as part of the library.
import Extraction.Basic

opaque P : Nat → Nat → Nat → Prop
opaque Q : Prop

/-- error: unknown free variable `_fvar.177` -/
#guard_msgs in
example (h : P 1 2 3 ↔ Q) : P 1 2 3 := by
  grind extract min_ast

/--
error: unsolved goals
⊢ P 1 2 3
-/
#guard_msgs in
theorem b : P 1 2 3 := by
  grind extract min_ast

/--
error: unsolved goals
⊢ [true] ++ [] = [false]
-/
#guard_msgs in
theorem a : [true] ++ [] = [false] := by
  grind extract min_ast
