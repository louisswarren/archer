open import Decidable

module Logic (X : Set) (_≟_ : Decidable≡ X) where

open import Ensemble
open import List
open import Tree

open import Deduction X _≟_
open import Formula   X _≟_
open import Models    X _≟_

-- Todo: prove completeness?

data Solved (α : Formula) : Set₁ where
  true  : ⊢ α → Solved α
  false : {l : List X} → (t : Tree l) → t ⊩̷ α → Solved α

soundness : ∀{Γ} → Assembled formulaEq Γ → ∀ α
            → Γ ⊢ α → ∀{l} → (t : Tree l) → (∀ γ → γ Ensemble.∈ Γ → t ⊩ γ) → t ⊩ α
soundness AΓ α (close AΔ Δ⊂Γ ⊢α) t t⊩Γ = soundness (assembled-context ⊢α) α ⊢α t λ γ γ∈Δ → t⊩Γ γ (stable∈ formulaEq {! AΓ  !} α (Δ⊂Γ γ γ∈Δ))
soundness AΓ α (assume .α) t t⊩Γ = t⊩Γ α refl
soundness AΓ (α ⇒ β) (arrowintro α ⊢α) leaf t⊩Γ with does leaf ⊩ α
...                                             | yes ⊩α = leaf (α ∣⇒ {!   !})
...                                             | no  ⊩̷α = {!   !}
soundness AΓ (α ⇒ β) (arrowintro α ⊢α) (branch x₁) t⊩Γ = {!   !}
soundness AΓ α (arrowelim ⊢α ⊢α₁) t = {!   !}
