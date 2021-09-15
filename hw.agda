open import lib

data Ctx : Set where
  ∙ : Ctx
  ext : Ctx → Ctx

Var : Ctx → Set
Var ∙ = ⊥
Var (ext Γ) = (Var Γ) + ⊤

data Tm (Γ : Ctx) : Type where
  var : Var Γ → Tm Γ
  app : Tm Γ → Tm Γ → Tm Γ
  abs : Tm (ext Γ) → Tm Γ
