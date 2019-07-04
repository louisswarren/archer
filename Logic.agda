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


-- A deduction problem Γ ⊢ α has an equivalent problem Δ ⊢ atom x, which is
-- obtained by assuming all premises in α

record Reduced {Γ : Ensemble Formula} (AΓ : Assembled formulaEq Γ) (α : Formula) : Set₁ where
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

