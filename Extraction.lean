-- This module serves as the root of the `Extraction` library.
-- Import modules here that should be built as part of the library.
import Extraction.Basic

#show_sketch (1 : Nat) + (2 |ₛ [3]ₛ)

example (f : Nat → Nat → Nat) : f (2 * 3) = f (2 + 2) := by
  grind extract (1 : Nat) |ₛ _
