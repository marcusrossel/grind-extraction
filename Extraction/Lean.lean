import Lean

def HEq.mp {α β : Sort u} (h : α ≍ β) (a : α) : β :=
  eq_of_heq h ▸ a

def Lean.Meta.mkHEqMP (heqProof pr : Expr) : MetaM Expr :=
  mkAppM ``HEq.mp #[heqProof, pr]

def Lean.Meta.mkEqHEqMP (eqHEqProof pr : Expr) : MetaM Expr := do
  let type ← inferType eqHEqProof
  if type.isEq then mkEqMP eqHEqProof pr else mkHEqMP eqHEqProof pr
