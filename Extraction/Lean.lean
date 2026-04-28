import Lean

def HEq.mp {α β : Sort u} (h : α ≍ β) (a : α) : β :=
  eq_of_heq h ▸ a

namespace Lean.Meta

def mkHEqMP (heqProof pr : Expr) : MetaM Expr :=
  mkAppM ``HEq.mp #[heqProof, pr]

def mkEqHEqMP (eqHEqProof pr : Expr) : MetaM Expr := do
  let type ← inferType eqHEqProof
  if type.isEq then mkEqMP eqHEqProof pr else mkHEqMP eqHEqProof pr

namespace Grind

@[inline] def firstInEqc? (rep : Expr) (f : Expr → GoalM (Option α)) : GoalM (Option α) := do
  let mut curr := rep
  repeat
    let node ← getENode curr
    let expr := node.self
    if let some suc ← f expr then return suc
    curr := node.next
    if isSameExpr curr rep then break
  return none

@[inline] def anyInEqc? (rep : Expr) (p : Expr → GoalM Bool) : GoalM Bool := do
  let any? ← firstInEqc? rep fun e => do
    if ← p e then
      return some ()
    else
      return none
  return any?.isSome
