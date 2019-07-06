open import Decidable

module Models (X : Set) (_≟_ : Decidable≡ X) where

open import Agda.Builtin.Sigma

open import Formula X _≟_
open import List
open import Tree


infix 1 _⊨_ _⊨̷_ _⊩_ _⊩̷_

data _⊨_ (xs : List X) : Formula → Set
data _⊨̷_ (xs : List X) : Formula → Set

data _⊨_ xs where
  atom  : ∀{x} → x List.∈ xs     → xs ⊨ atom x
  _∣⇒_  : ∀{β} → ∀ α    → xs ⊨ β → xs ⊨ (α ⇒ β)
  _⇒∣_  : ∀{α} → xs ⊨̷ α → ∀ β    → xs ⊨ (α ⇒ β)

data _⊨̷_ xs where
  atom : ∀{x}   → x List.∉ xs     → xs ⊨̷ atom x
  _⇒_  : ∀{α β} → xs ⊨ α → xs ⊨̷ β → xs ⊨̷ (α ⇒ β)

-- Note that the above classical entailment is NOT monotone in a Kripke tree


data _⊩_ {l : List X} : Tree l → Formula → Set where
  leaf   : ∀{α}    → l ⊨ α                        → leaf      ⊩ α
  branch : ∀{α ts} → l ⊨ α → All ((_⊩ α) ∘lop) ts → branch ts ⊩ α

data _⊩̷_ {l : List X} : Tree l → Formula → Set where
  root   : ∀{α t}  → l ⊨̷ α                → t         ⊩̷ α
  branch : ∀{α ts} → Any ((_⊩̷ α) ∘lop) ts → branch ts ⊩̷ α


monotone⊩ : ∀ α → Monotone (_⊩ α)
monotone⊩ α t .t root t⊩α = t⊩α
monotone⊩ α (branch ts) t′ (branch t∈ts t≼t′) (branch _ ts⊩α)
    = monotone⊩ α _ t′ t≼t′ (∈All ts⊩α t∈ts)
  where
    ∈All : {A : Set} {P : A → Set} {x : A} {xs : List A}
           → All P xs → x ∈ xs → P x
    ∈All (Px ∷ Pxs) [ refl ]    = Px
    ∈All (_  ∷ Pxs) (_ ∷ x∈xxs) = ∈All Pxs x∈xxs
