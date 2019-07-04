open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Sigma

open import Decidable
open import Ensemble
open import List
open import Tree

module Logic (X : Set) (_≟_ : Decidable≡ X) where

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


infix 1 _⊢_ _⊩_ _⊩̷_
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



reduce : ∀ Γ α → Assembled formulaEq Γ → Σ (Ensemble Formula) λ Δ → Σ X λ x → Δ ⊢ (atom x) → Γ ⊢ α
reduce Γ (atom x) AΓ = Γ , x , λ ⊢x → close AΓ (λ x z z₁ → z₁ z) ⊢x
reduce Γ (α ⇒ β)  AΓ = Δ , x , λ ⊢x → close AΓ cls (arrowintro α (ρ ⊢x))
  where
    ind : _
    ind = reduce (Γ ∪ ⟨ α ⟩) β (from AΓ ∪ from⟨ α ⟩)
    Δ : Ensemble Formula
    Δ = fst ind
    x : X
    x = fst (snd ind)
    ρ : Δ ⊢ atom x → Γ ∪ ⟨ α ⟩ ⊢ β
    ρ = snd (snd ind)
    cls : (Γ ∪ ⟨ α ⟩) - α ⊂ Γ
    cls = λ x₁ z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂)


data [_]⊩_ (xs : List X) : Formula → Set
data [_]⊩̷_ (xs : List X) : Formula → Set

data [_]⊩_ xs where
  atom : ∀{x} → x List.∈ xs → [ xs ]⊩ atom x
  _∣⇒_  : ∀{β} → ∀ α → [ xs ]⊩ β → [ xs ]⊩ (α ⇒ β)
  _⇒∣_  : ∀{α} → [ xs ]⊩̷ α → ∀ β → [ xs ]⊩ (α ⇒ β)

data [_]⊩̷_ xs where
  atom : ∀{x} → x List.∉ xs → [ xs ]⊩̷ atom x
  _⇒_  : ∀{α β} → [ xs ]⊩ α → [ xs ]⊩̷ β → [ xs ]⊩̷ (α ⇒ β)


data _⊩_ {l} : Tree l → Formula → Set where
  leaf   : ∀{α} → [ l ]⊩ α → leaf ⊩ α
  branch : ∀{ts α} → [ l ]⊩ α → List.All (λ { (s , t) → t ⊩ α }) ts → branch ts ⊩ α

data _⊩̷_ {l} : Tree l → Formula → Set where
  here  : ∀{t α} → [ l ]⊩̷ α → t ⊩̷ α
  later : ∀{ts α} → List.Any (λ { (s , t) → t ⊩ α }) ts → branch ts ⊩̷ α


-- Confirm that local non-forcing is equivalent to not forcing
[_]⊩̷_neg : (l : List X) → (α : Formula) → [ l ]⊩̷ α → ¬ [ l ]⊩ α
[ l ]⊩̷ atom x neg (atom x∉l) (atom x∈l) = x∉l x∈l
[ l ]⊩̷ α ⇒ β neg (⊩α ⇒ ⊩̷β) (.α ∣⇒ ⊩β) = [ l ]⊩̷ β neg ⊩̷β ⊩β
[ l ]⊩̷ α ⇒ β neg (⊩α ⇒ ⊩̷β) (⊩̷α ⇒∣ .β) = [ l ]⊩̷ α neg ⊩̷α ⊩α

¬[_]⊩_pos : (l : List X) → (α : Formula) → ¬ [ l ]⊩ α → [ l ]⊩̷ α

decide[_]⊩_ : (l : List X) → (α : Formula) → Dec ([ l ]⊩ α)
decide[ l ]⊩ atom x  with List.decide∈ _≟_ x l
...                  | yes x∈l = yes (atom x∈l)
...                  | no  x∉l = no λ { (atom x∈l) → x∉l x∈l }
decide[ l ]⊩ (α ⇒ β) with decide[ l ]⊩ α | decide[ l ]⊩ β
...                  | _      | yes ⊩β = yes (α ∣⇒ ⊩β)
...                  | no ¬⊩α | _      = yes (¬[ l ]⊩ α pos ¬⊩α ⇒∣ β)
...                  | yes ⊩α | no ¬⊩β = no λ { (α ∣⇒ ⊩β) → ¬⊩β ⊩β
                                              ; (⊩̷α ⇒∣ β) → [ l ]⊩̷ α neg ⊩̷α ⊩α }

¬[ l ]⊩ atom x pos nf = atom (λ z → nf (atom z))
¬[ l ]⊩ α ⇒ β pos nf with decide[ l ]⊩ α | decide[ l ]⊩ β
¬[ l ]⊩ α ⇒ β pos nf | yes ⊩α | no ¬⊩β = ⊩α ⇒ ¬[ l ]⊩ β pos ¬⊩β
¬[ l ]⊩ α ⇒ β pos nf | _      | yes ⊩β = ⊥-elim (nf (α ∣⇒ ⊩β))
¬[ l ]⊩ α ⇒ β pos nf | no ¬⊩α | _      = ⊥-elim (nf (¬[ l ]⊩ α pos ¬⊩α ⇒∣ β))

