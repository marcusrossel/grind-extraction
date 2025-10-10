-- This module serves as the root of the `Extraction` library.
-- Import modules here that should be built as part of the library.
import Extraction.Basic

#show_sketch (1 : Nat) + (2 |ₛ [3]ₛ)

opaque P : Nat → Nat → Nat → Prop
opaque Q : Prop

/-- error: failed, but found equivalent Q -/
#guard_msgs in
example (h : P 1 2 3 ↔ Q) : P 1 2 3 := by
  grind extract _
