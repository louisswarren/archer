open import Decidable

module Deduction (X : Set) (_≟_ : Decidable≡ X) where

open import Ensemble

open import Formula X _≟_

infix 1 _⊢_ ⊢_
data _⊢_ : Ensemble Formula → Formula → Set₁ where
  close       : ∀{Γ Δ α} → Assembled formulaEq Δ → Γ ⊂ Δ → Γ ⊢ α → Δ ⊢ α

  assume      : (α : Formula)
                →                               ⟨ α ⟩ ⊢ α

  arrowintro  : ∀{Γ β} → (α : Formula)
                →                                 Γ ⊢ β
                                             --------------- ⇒⁺
                →                             Γ - α ⊢ α ⇒ β

  arrowelim   : ∀{Γ₁ Γ₂ α β}
                →                       Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                                       --------------------------- ⇒⁻
                →                              Γ₁ ∪ Γ₂ ⊢ β

⊢_ : Formula → Set₁
⊢ α = ∅ ⊢ α

-- A deduction problem Γ ⊢ α has an equivalent problem Δ ⊢ atom x, which is
-- obtained by assuming all premises in α

record Reduced {Γ} (AΓ : Assembled formulaEq Γ) (α : Formula) : Set₁ where
  constructor reduced
  field
    Δ   : Ensemble Formula
    AΔ  : Assembled formulaEq Δ
    x   : X
    ⟨→⟩ : Δ ⊢ atom x → Γ ⊢ α
    ⟨←⟩ : Γ ⊢ α → Δ ⊢ atom x

reduce : ∀{Γ} → ∀ AΓ α → Reduced {Γ} AΓ α
reduce {Γ} AΓ (atom x) = reduced Γ AΓ x (λ ⊢x → ⊢x) λ ⊢x → ⊢x
reduce {Γ} AΓ (α ⇒ β)  = reduced
                          (Reduced.Δ ind)
                          (Reduced.AΔ ind)
                          (Reduced.x ind)
                          (λ Δ⊢x
                           → close AΓ Γ∪α-α⊂Γ
                              (arrowintro α
                               (Reduced.⟨→⟩ ind
                                Δ⊢x)))
                          (λ Γ⊢α⇒β
                           → close (Reduced.AΔ ind) Δ⊂Δ
                              (Reduced.⟨←⟩ ind
                               (arrowelim
                                Γ⊢α⇒β
                                (assume α))))
  where
    ind : _
    ind = reduce (from AΓ ∪ from⟨ α ⟩) β
    Γ∪α-α⊂Γ : (Γ ∪ ⟨ α ⟩) - α ⊂ Γ
    Γ∪α-α⊂Γ = λ x₁ z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂)
    Δ⊂Δ : Reduced.Δ ind ⊂ Reduced.Δ ind
    Δ⊂Δ = λ x z z₁ → z₁ z

