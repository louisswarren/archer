open import Agda.Builtin.Equality public

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬(x ≡ y)

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

Pred : Set → Set₁
Pred A = A → Set

Decidable : {A : Set} → Pred A → Set
Decidable P = ∀ x → Dec (P x)

record Discrete (A : Set) : Set where
  constructor discrete
  field
    _⟨_≟_⟩ : (x y : A) → Dec (x ≡ y)
open Discrete public

_≟_ : {A : Set} ⦃ _ : Discrete A ⦄ → (x y : A) → Dec (x ≡ y)
_≟_ ⦃ d ⦄ x y = d ⟨ x ≟ y ⟩
