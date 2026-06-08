import Lean

def Array.pop? (as : Array α) : Option (α × Array α) :=
  if _ : 0 < as.size then
    some (as.back, as.pop)
  else
    none

def HEq.mp {α β : Sort u} (h : α ≍ β) (a : α) : β :=
  eq_of_heq h ▸ a

namespace Lean

def Expr.getFnArg? (e : Expr) : (Option Expr) × Expr := Id.run do
  let .app fn arg := e | return (none, e)
  return (fn, arg)

namespace Meta

def mkHEqMP (heqProof pr : Expr) : MetaM Expr :=
  mkAppM ``HEq.mp #[heqProof, pr]

def mkEqHEqMP (eqHEqProof pr : Expr) : MetaM Expr := do
  let type ← inferType eqHEqProof
  if type.isEq then mkEqMP eqHEqProof pr else mkHEqMP eqHEqProof pr

deriving instance Inhabited for Sym.ExprPtr

namespace Grind

def getRootPtr (e : Expr) : GoalM ExprPtr := do
  let root ← getRoot e
  return ⟨root⟩

def getRootPtr? (e : Expr) : GoalM (Option ExprPtr) := do
  let some root ← getRoot? e | return none
  return some ⟨root⟩

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
