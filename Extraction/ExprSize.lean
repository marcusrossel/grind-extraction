import Lean

namespace Lean.Meta.Grind.Extraction

/--
Special constants which force applications to have a fixed cost. For example, we want the
application `@OfNat.ofNat α n inst` to have a fixed cost of `1` instead of accounting for the sizes
of `α`, `n` and `inst`.
-/
def fixedAppSize? (e : Expr) : Option Nat :=
  match_expr e with
  | False             => some 1000000000000000
  | OfNat.ofNat _ _ _ => some 1
  | _                 => none

/--
We use this size function instead of `Expr.sizeWithoutSharing` to more closely match the size which
is computed (incrementally) by `extractMinAST.assign`. This implementation will likely change in the
future.
-/
def exprSize (e : Expr) : Nat :=
  if let some fixed := fixedAppSize? e then
    fixed
  else
    match e with
    | .app fn arg               => exprSize fn + exprSize arg
    | .lam _ dom body _         => exprSize dom + exprSize body
    | .forallE _ dom body _     => exprSize dom + exprSize body
    | .letE _ type value body _ => exprSize type + exprSize value + exprSize body
    | .mdata _ e                => exprSize e
    | .proj _ _ s               => exprSize s + 1
    | _                         => 1

structure SizedExpr where
  expr : Expr
  size : Nat
  deriving Inhabited

instance SizedExpr.instToMessageData : ToMessageData SizedExpr where
  toMessageData e := m!"[{e.size}] {e.expr}"

instance : Coe SizedExpr MessageData where
  coe := toMessageData

def _root_.Lean.Expr.toSized (e : Expr) : SizedExpr where
  expr := e
  size := exprSize e
