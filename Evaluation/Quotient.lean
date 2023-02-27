import Lean
import EggTactic 

/-- Small example to test rewriting quotients. It'd be similar with minimization
problems. -/

structure RawConstr where 
  D : Type 
  val : D → Prop 

structure Equiv (cs₁ cs₂ : RawConstr) where 
  phi : cs₁.D → cs₂.D
  psi : cs₂.D → cs₁.D
  phi_feas : ∀ x, cs₁.val x → cs₂.val (phi x)
  psi_feas : ∀ x, cs₂.val x → cs₁.val (psi x) 

def Equiv.refl (cs : RawConstr) : Equiv cs cs := 
  ⟨id, id, fun _ h => h, fun _ h => h⟩

def Equiv.symm {cs₁ cs₂ : RawConstr} (e : Equiv cs₁ cs₂) : Equiv cs₂ cs₁ := 
  ⟨e.psi, e.phi, e.psi_feas, e.phi_feas⟩

def Equiv.trans {cs₁ cs₂ cs₃ : RawConstr} 
  (e₁ : Equiv cs₁ cs₂) (e₂ : Equiv cs₂ cs₃) : Equiv cs₁ cs₃ := 
  ⟨e₂.phi ∘ e₁.phi, e₁.psi ∘ e₂.psi, 
    fun _ h => e₂.phi_feas _ (e₁.phi_feas _ h), 
    fun _ h => e₁.psi_feas _ (e₂.psi_feas _ h)⟩

def RawConstr.equiv (cs₁ cs₂ : RawConstr) : Prop := 
  Nonempty (Equiv cs₁ cs₂)

def RawConstr.equiv_refl (cs : RawConstr) : RawConstr.equiv cs cs := 
  ⟨Equiv.refl cs⟩

def RawConstr.equiv_symm {cs₁ cs₂ : RawConstr} :
  RawConstr.equiv cs₁ cs₂ → RawConstr.equiv cs₂ cs₁ := 
  fun ⟨e⟩ => ⟨Equiv.symm e⟩

def RawConstr.equiv_trans {cs₁ cs₂ cs₃ : RawConstr} :
  RawConstr.equiv cs₁ cs₂ → RawConstr.equiv cs₂ cs₃ → RawConstr.equiv cs₁ cs₃ :=
  fun ⟨e₁⟩ ⟨e₂⟩ => ⟨Equiv.trans e₁ e₂⟩   

instance : Setoid RawConstr := 
  { r := RawConstr.equiv, 
    iseqv := 
      { refl := RawConstr.equiv_refl, 
        symm := RawConstr.equiv_symm, 
        trans := RawConstr.equiv_trans } }

def Constr := @Quotient RawConstr (by infer_instance)

def Constr.mk {D : Type} (val : D → Prop) : Constr := 
  Quotient.mk' (RawConstr.mk D val)

notation:max "⦃" cs "⦄" => Constr.mk cs

#check ⦃ fun _ => True ⦄

theorem Constr.comm {D : Type} {cs₁ cs₂ : D → Prop} : 
  ⦃ fun x => cs₁ x ∧ cs₂ x ⦄ = ⦃ fun x => cs₂ x ∧ cs₁ x ⦄ := 
  Quotient.sound <| Nonempty.intro <| {
    phi := id, psi := id,
    phi_feas := fun _ h => ⟨h.2, h.1⟩,
    psi_feas := fun _ h => ⟨h.2, h.1⟩ }

theorem Constr.assoc {D : Type} {cs₁ cs₂ cs₃ : D → Prop} : 
  ⦃ fun x => (cs₁ x ∧ cs₂ x) ∧ cs₃ x ⦄ = ⦃ fun x => cs₁ x ∧ (cs₂ x ∧ cs₃ x) ⦄ := 
  Quotient.sound <| Nonempty.intro <| {
    phi := id, psi := id,
    phi_feas := fun _ h => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩,
    psi_feas := fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩ }

section Test

set_option trace.EggTactic.egg true

def a : Prop := sorry
def b : Prop := sorry
def c : Prop := sorry

example : ⦃ fun (_ : Nat) => a ∧ b  ⦄ = ⦃ fun (_ : Nat) => b ∧ a ⦄ := 
  by eggxplosion [Constr.comm]

theorem comm_thm
  (constr_comm : ∀  {D : Type} {cs₁ cs₂ : D → Prop}, 
    ⦃ fun x => cs₁ x ∧ cs₂ x ⦄ = ⦃ fun x => cs₂ x ∧ cs₁ x ⦄)
  (a b : Nat → Prop) : 
  ⦃ fun (x : Nat) => a x ∧ b x ⦄ = ⦃ fun (x : Nat) => b x ∧ a x ⦄ :=
  by eggxplosion [constr_comm]

#print comm_thm

theorem comm_thm'
  (constr_comm : ∀  {D : Type} {cs₁ cs₂ : D → Prop}, 
    ⦃ fun x => cs₁ x ∧ cs₂ x ⦄ = ⦃ fun x => cs₂ x ∧ cs₁ x ⦄)
  (a : Nat → Prop) (b : Prop) : 
  ⦃ fun (x : Nat) => a x ∧ b ⦄ = ⦃ fun (x : Nat) => b ∧ a x ⦄ :=
  by eggxplosion [constr_comm]

theorem comm_assoc_thm 
  (constr_comm : ∀  {D : Type} {cs₁ cs₂ : D → Prop}, 
    ⦃ fun x => cs₁ x ∧ cs₂ x ⦄ = ⦃ fun x => cs₂ x ∧ cs₁ x ⦄)
  (constr_assoc : ∀  {D : Type} {cs₁ cs₂ cs₃ : D → Prop},
    ⦃ fun x => (cs₁ x ∧ cs₂ x) ∧ cs₃ x ⦄ = ⦃ fun x => cs₁ x ∧ (cs₂ x ∧ cs₃ x) ⦄)
  (a b c : Nat → Prop) :
  ⦃ fun (x : Nat) => a x ∧ b x ∧ c x ⦄ = ⦃ fun (x : Nat) => c x ∧ a x ∧ b x ⦄ :=
  by eggxplosion [constr_comm, constr_assoc]

theorem comm_assoc_thm' 
  (constr_comm : ∀  {D : Type} {cs₁ cs₂ : D → Prop}, 
    ⦃ fun x => cs₁ x ∧ cs₂ x ⦄ = ⦃ fun x => cs₂ x ∧ cs₁ x ⦄)
  (constr_comm' : ∀ {D : Type} {cs cs₁ cs₂ : D → Prop}, 
    ⦃ fun x => cs x ∧ (cs₁ x ∧ cs₂ x) ⦄ = ⦃ fun x => cs x ∧ (cs₂ x ∧ cs₁ x) ⦄)
  (constr_assoc : ∀  {D : Type} {cs₁ cs₂ cs₃ : D → Prop},
    ⦃ fun x => (cs₁ x ∧ cs₂ x) ∧ cs₃ x ⦄ = ⦃ fun x => cs₁ x ∧ (cs₂ x ∧ cs₃ x) ⦄)
  (a b c : Nat → Prop) :
  ⦃ fun (x : Nat) => a x ∧ b x ∧ c x ⦄ = ⦃ fun (x : Nat) => c x ∧ a x ∧ b x ⦄ :=
  by eggxplosion [constr_comm, constr_comm', constr_assoc]

end Test
