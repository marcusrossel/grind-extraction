-- This module serves as the root of the `Extraction` library.
-- Import modules here that should be built as part of the library.
import Extraction.Basic

inductive P : Nat → Nat → Nat → Prop
  | intro : P 1 2 3

inductive Q : Prop
  | intro

@[grind =]
theorem p_iff_q : P 1 2 3 ↔ Q := by
  simp [P.intro, Q.intro]

example : P 1 2 3 := by
  grind extract min_ast
  constructor
