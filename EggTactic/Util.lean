import Lean

open Lean Meta

def _root_.List.revLookup? {α β : Type 0} [BEq β] : List (α × β) → β → Option α
  | [], _ => none
  | (a, b) :: rest, b' => if b == b' then some a else rest.revLookup? b'

def _root_.List.unique {α : Type 0} [BEq α] : List α → List α
  | [] => []
  | a :: as => if as.contains a then as.unique else (a :: as.unique)

def _root_.List.unzip3 {α β γ : Type 0} : 
  List (α × β × γ) → List α × List β × List γ
  | abc => 
      let (a, bc) := abc.unzip 
      (a, bc.unzip)

def _root_.Lean.Meta.matchEquiv? (e : Expr) : 
  MetaM (Option (Expr × Expr × Expr)) := do
  match e with 
  | Expr.app (Expr.app (Expr.app (Expr.const _ _) _) _) _ =>
      let ty := e.appFn!.appFn!.appArg!
      let instExpr ← mkAppM `Setoid #[ty]
      try 
        let i ← synthInstance (← whnf instExpr)
        let lhs := e.appFn!.appArg!
        let rhs := e.appArg!
        return some (i, lhs, rhs)
      catch _ => return none
  | _ => return none
