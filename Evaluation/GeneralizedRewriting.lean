import EggTactic

inductive EQ {α : Type} (a : α) : α → Type where
  | refl : EQ a a

def EQ.trans {a b c : α} (h₁ : EQ a b) (h₂ : EQ b c) : EQ a c := by
  cases h₁; exact h₂ 

instance : Trans (@EQ α) (@EQ α) (@EQ α) where
  trans := EQ.trans

infix:50 " ≋ " => EQ

example (h₁ : EQ a b) (h₂ : b = c) (h₃ : EQ c d) : EQ a d := by
  calc a ≋ b := h₁
       _ = c := h₂
       _ ≋ d := h₃

example (h₁ : EQ a b) (h₂ : b = c) (h₃ : EQ c d) : EQ a d := by
  eggxplosion [h₁, h₂, h₃]
