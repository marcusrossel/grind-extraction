import Lean

namespace Lean.Meta.Grind.Extraction

inductive Cost where
  | nat (n : Nat)
  | inf
  deriving Inhabited

namespace Cost

instance : ToString Cost where
  toString
    | nat n => toString n
    | inf   => "∞"

instance : Coe Nat Cost where
  coe := nat

instance : OfNat Cost n where
  ofNat := n

def add : Cost → Cost → Cost
  | nat n₁, nat n₂ => n₁ + n₂
  | _, _           => inf

instance : Add Cost where
  add := add

def lt : Cost → Cost → Bool
  | nat n₁, nat n₂ => n₁ < n₂
  | nat _,  inf    => true
  | _,      _      => false

instance : LT Cost where
  lt c₁ c₂ := c₁.lt c₂

instance : DecidableLT Cost :=
  fun _ _ => decidable_of_bool _ Iff.rfl

end Cost

/--
A cost function assigns a cost to an e-node (`Expr`) given the costs of its children `Array Cost`.
-/
abbrev CostFn := Expr → (Array Cost) → Cost
