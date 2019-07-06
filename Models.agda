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
  atom : ∀{x} → x List.∈ xs → xs ⊨ atom x
  _∣⇒_  : ∀{β} → ∀ α → xs ⊨ β → xs ⊨ (α ⇒ β)
  _⇒∣_  : ∀{α} → xs ⊨̷ α → ∀ β → xs ⊨ (α ⇒ β)

data _⊨̷_ xs where
  atom : ∀{x} → x List.∉ xs → xs ⊨̷ atom x
  _⇒_  : ∀{α β} → xs ⊨ α → xs ⊨̷ β → xs ⊨̷ (α ⇒ β)

-- Note that the above classical entailment is NOT monotone in a Kripke tree


data _⊩_ {l : List X} : Tree l → Formula → Set where
  leaf   : ∀{α}    → l ⊨ α                        → leaf      ⊩ α
  branch : ∀{α ts} → l ⊨ α → All ((_⊩ α) ∘lop) ts → branch ts ⊩ α

data _⊩̷_ {l : List X} : Tree l → Formula → Set where
  root   : ∀{α t}  → l ⊨̷ α → t ⊩̷ α
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



--data DecLocallyForces (l : List X) (α : Formula) : Set where
--  yes : l ⊨ α → DecLocallyForces l α
--  no  : l ⊨̷ α → DecLocallyForces l α
--
--data DecForces {l} (t : Tree l) (α : Formula) : Set where
--  yes : t ⊩ α → DecForces t α
--  no  : t ⊩̷ α → DecForces t α
--
--_⊨?_ : (l : List X) → (α : Formula) → DecLocallyForces l α
--l ⊨? atom x  with List.decide∈ _≟_ x l
--...             | yes x∈l = yes (atom x∈l)
--...             | no  x∉l = no  (atom x∉l)
--l ⊨? (α ⇒ β) with l ⊨? α | l ⊨? β
--...             | _      | yes ⊨β = yes (α ∣⇒ ⊨β)
--...             | no ⊨̷α  | _      = yes (⊨̷α ⇒∣ β)
--...             | yes ⊨α | no ⊨̷β  = no (⊨α ⇒ ⊨̷β)
--
--_⊩?_ : ∀{l} → (t : Tree l) → (α : Formula) → DecForces t α
--_⊩?_ {l} t α with l ⊨? α
--leaf        ⊩? α | yes [l]⊩α = yes (leaf [l]⊩α)
--(branch ts) ⊩? α | yes [l]⊩α = yes {!   !}
--t ⊩? α           | no  [l]⊩̷α = {!   !}
--
--
------ Confirm that local non-forcing is equivalent to not forcing
----_⊨̷_neg : (l : List X) → (α : Formula) → l ⊨̷ α → ¬ l ⊩ α
----l ⊨̷ atom x neg (atom x∉l) (atom x∈l) = x∉l x∈l
----l ⊨̷ α ⇒ β neg (⊩α ⇒ ⊩̷β) (.α ∣⇒ ⊩β) = l ⊨̷ β neg ⊩̷β ⊩β
----l ⊨̷ α ⇒ β neg (⊩α ⇒ ⊩̷β) (⊩̷α ⇒∣ .β) = l ⊨̷ α neg ⊩̷α ⊩α
----
----¬_⊨_pos : (l : List X) → (α : Formula) → ¬ l ⊩ α → l ⊨̷ α
----
----decide_⊩_ : (l : List X) → (α : Formula) → Dec (l ⊩ α)
----decide l ⊩ atom x  with List.decide∈ _≟_ x l
----...                  | yes x∈l = yes (atom x∈l)
----...                  | no  x∉l = no λ { (atom x∈l) → x∉l x∈l }
----decide l ⊩ (α ⇒ β) with decide l ⊩ α | decide l ⊩ β
----...                  | _      | yes ⊩β = yes (α ∣⇒ ⊩β)
----...                  | no ¬⊩α | _      = yes (¬l ⊩ α pos ¬⊩α ⇒∣ β)
----...                  | yes ⊩α | no ¬⊩β = no λ { (α ∣⇒ ⊩β) → ¬⊩β ⊩β
----                                              ; (⊩̷α ⇒∣ β) → l ⊨̷ α neg ⊩̷α ⊩α }
----
----¬ l ⊩ atom x pos nf = atom (λ z → nf (atom z))
----¬ l ⊩ α ⇒ β pos nf with decidel ⊩ α | decidel ⊩ β
----¬ l ⊩ α ⇒ β pos nf | yes ⊩α | no ¬⊩β = ⊩α ⇒ ¬l ⊩ β pos ¬⊩β
----¬ l ⊩ α ⇒ β pos nf | _      | yes ⊩β = ⊥-elim (nf (α ∣⇒ ⊩β))
----¬ l ⊩ α ⇒ β pos nf | no ¬⊩α | _      = ⊥-elim (nf (¬l ⊩ α pos ¬⊩α ⇒∣ β))
----
------ Confirm that non-forcing is equivalent to not forcing
----
----_⊩̷_neg : ∀{l} → (t : Tree l) → (α : Formula) → t ⊩̷ α → ¬ (t ⊩ α)
----(leaf ⊩̷ α neg) (here [l]⊩̷α) (leaf [l]⊩α) = [ _ ]⊩̷ α neg [l]⊩̷α [l]⊩α
----(branch x ⊩̷ α neg) (here [l]⊩̷α) (branch [l]⊩α _) = [ _ ]⊩̷ α neg [l]⊩̷α [l]⊩α
----(branch .(_ ∷ _) ⊩̷ α neg) (later [ t⊩̷α ]) (branch _ (t⊩α ∷ _)) = (_ ⊩̷ α neg) t⊩̷α t⊩α
----(branch (_ ∷ ts) ⊩̷ α neg) (later (_ ∷ ∃ts⊩̷α)) (branch [l]⊩α (_ ∷ ts⊩α)) = (branch ts ⊩̷ α neg) (later ∃ts⊩̷α) (branch [l]⊩α ts⊩α)
----
