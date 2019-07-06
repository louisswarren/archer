open import Decidable

module Formula (X : Set) (_≟_ : Decidable≡ X) where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat renaming (Nat to ℕ)


infixr 105 _⇒_
data Formula : Set where
  atom : X → Formula
  _⇒_  : Formula → Formula → Formula

formulaEq : Decidable≡ Formula
formulaEq (atom x) (atom y) with x ≟ y
...                         | yes refl = yes refl
...                         | no  x≢y  = no λ { refl → x≢y refl }
formulaEq (α ⇒ β)  (γ ⇒ δ)  with formulaEq α γ | formulaEq β δ
...                         | yes refl | yes refl = yes refl
...                         | _        | no γ≢δ   = no λ { refl → γ≢δ refl }
...                         | no α≢β   | _        = no λ { refl → α≢β refl }
formulaEq (atom _) (_ ⇒ _)  = no λ ()
formulaEq (_ ⇒ _)  (atom _) = no λ ()


∣_∣ : Formula → ℕ
∣ atom _       ∣ = zero
∣ (atom _) ⇒ β ∣ = ∣ β ∣
∣ (_ ⇒ _ ) ⇒ β ∣ = suc ∣ β ∣

SimpleFormula : Formula → Set
SimpleFormula α = ∣ α ∣ ≡ zero

LeftFormula : Formula → Set
LeftFormula α = Σ ℕ λ k → ∣ α ∣ ≡ suc k
