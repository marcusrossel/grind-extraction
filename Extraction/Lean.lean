import Lean

def HEq.mp {α β : Sort u} (h : α ≍ β) (a : α) : β :=
  eq_of_heq h ▸ a

namespace Lean.Meta

def mkHEqMP (heqProof pr : Expr) : MetaM Expr :=
  mkAppM ``HEq.mp #[heqProof, pr]

def mkEqHEqMP (eqHEqProof pr : Expr) : MetaM Expr := do
  let type ← inferType eqHEqProof
  if type.isEq then mkEqMP eqHEqProof pr else mkHEqMP eqHEqProof pr

@[inline] def Grind.firstInEqc? (rep : Expr) (f : Expr → GoalM (Option Expr)) :
    GoalM (Option Expr) := do
  let mut curr := rep
  repeat
    let node ← getENode curr
    let expr := node.self
    if let some suc ← f expr then return suc
    curr := node.next
    if isSameExpr curr rep then break
  return none
