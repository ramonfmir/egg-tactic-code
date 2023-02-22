import EggTactic

open Lean Elab Meta Tactic Term

theorem equiv_eq {A : Type} [Setoid A] (a b c d : A) 
  (hab : a ≈ b) (hac : a ≈ c) (hbd : b ≈ d) : 
  (a ≈ b) = (c ≈ d) := 
  propext ⟨
    fun _ => Setoid.trans (Setoid.trans (Setoid.symm hac) hab) hbd, 
    fun _ => hab⟩ 

def Lean.Meta.matchEquiv? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
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

section Test

def r : ∀ {α : Type}, α → α → Prop := sorry

def A : Type := sorry

def x : A := sorry

instance : Setoid A := {
  r := @r A,
  iseqv := sorry
}

def e : Expr := mkApp3 (mkConst `Avo) (mkConst `A) (mkConst `x) (mkConst `x)

#eval do 
  let x ← Lean.Meta.matchEquiv? e
  IO.println x

#check Lean.MVarId.replaceTargetEq

-- Hacky way of having generalized rewriting?
theorem rw_test (a b : A) [Setoid A] (h : a ≈ b) : b ≈ a := by
  rw [equiv_eq b a a b (Setoid.symm h) (Setoid.symm h) h]
  assumption

end Test
