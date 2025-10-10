-- This module serves as the root of the `Extraction` library.
-- Import modules here that should be built as part of the library.
import Extraction.Basic

#show_sketch (1 : Nat) + (2 |ₛ [3]ₛ)

opaque P : Nat → Nat → Nat → Prop
opaque Q : Prop
opaque R : Nat → Prop

example (h : P 1 2 3 ↔ Q) (h2 : P 1 2 3 ↔ R 1) : P 1 2 3 := by
  grind extract min_ast
