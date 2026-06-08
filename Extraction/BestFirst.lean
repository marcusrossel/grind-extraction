import Extraction.Lean
open Std

namespace Lean.Meta.Grind.Extraction

/--
A cost function maps an application of `head` to children with costs `args?` to a `Nat` cost. If the
`args?` are not provided, i.e. they are `none`, then the function should return a lower bound on the
cost of the application. For example, if we know that a head symbol `append` always incurs a cost of
`1`, then an application of `append` should return a lower cost bound of `1`.
-/
abbrev CostFn := (head : Expr) → (args? : Option <| Array Nat) → Nat

def CostFn.leaf (cost : CostFn) (e : Expr) : Nat :=
  cost e (some #[])
