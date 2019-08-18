open import Decidable

module Models (X : Set) (_≟_ : Decidable≡ X) where

open import Agda.Builtin.Sigma

open import List
open import Tree

open import Formula X _≟_


infix 1 _⊨_ _⊨̷_ _⊩_ _⊩̷_

data _⊨_ (l : List X) : Formula → Set
data _⊨̷_ (l : List X) : Formula → Set

data _⊨_ l where
  atom  : ∀{x} → x List.∈ l     → l ⊨ atom x
  _∣⇒_  : ∀{β} → ∀ α    → l ⊨ β → l ⊨ (α ⇒ β)
  _⇒∣_  : ∀{α} → l ⊨̷ α → ∀ β    → l ⊨ (α ⇒ β)

data _⊨̷_ l where
  atom : ∀{x}   → x List.∉ l     → l ⊨̷ atom x
  _⇒_  : ∀{α β} → l ⊨ α → l ⊨̷ β → l ⊨̷ (α ⇒ β)

data Does_⊨_ (l : List X) (α : Formula) : Set where
  yes : l ⊨ α → Does l ⊨ α
  no  : l ⊨̷ α → Does l ⊨ α

does_⊨_ : (l : List X) → (α : Formula) → Does l ⊨ α
does l ⊨ atom x  with decide∈ _≟_ x l
...              | yes x∈l = yes (atom x∈l)
...              | no  x∉l = no  (atom x∉l)
does l ⊨ (α ⇒ β) with does l ⊨ α | does l ⊨ β
...              | _      | yes ⊨β = yes (α ∣⇒ ⊨β)
...              | no  ⊨̷α | _      = yes (⊨̷α ⇒∣ β)
...              | yes ⊨α | no ⊨̷β  = no  (⊨α ⇒ ⊨̷β)


-- Note that the above classical entailment is NOT monotone in a Kripke tree


data _⊩_ {l : List X} : Tree l → Formula → Set where
  leaf   : ∀{α}    → l ⊨ α                        → leaf      ⊩ α
  branch : ∀{α ts} → l ⊨ α → All ((_⊩ α) ∘lop) ts → branch ts ⊩ α

data _⊩̷_ {l : List X} : Tree l → Formula → Set where
  root   : ∀{α t}  → l ⊨̷ α                → t         ⊩̷ α
  branch : ∀{α ts} → Any ((_⊩̷ α) ∘lop) ts → branch ts ⊩̷ α

data Does_⊩_ {l : List X} (t : Tree l) (α : Formula) : Set where
  yes : t ⊩ α → Does t ⊩ α
  no  : t ⊩̷ α → Does t ⊩ α

data DoesEvery_⊩_ {l : List X} (ts : List (Subtree l)) (α : Formula) : Set where
  yes : All ((_⊩ α) ∘lop) ts → DoesEvery ts ⊩ α
  no  : Any ((_⊩̷ α) ∘lop) ts → DoesEvery ts ⊩ α

does_⊩_ : {l : List X} → (t : Tree l) → (α : Formula) → Does t ⊩ α

doesevery_⊩_ : {l : List X} → (ts : List (Subtree l)) → (α : Formula) → DoesEvery ts ⊩ α
doesevery [] ⊩ α = yes []
doesevery (s , t) ∷ ts ⊩ α with does t ⊩ α
...                        | no  t⊩̷α = no [ t⊩̷α ]
...                        | yes t⊩α with doesevery ts ⊩ α
...                                  | yes ts⊩α = yes (t⊩α ∷ ts⊩α)
...                                  | no  ts⊩̷α = no ((s , t) ∷ ts⊩̷α)

does_⊩_ {l} leaf α with does l ⊨ α
...                | yes ⊨α = yes (leaf ⊨α)
...                | no  ⊨̷α = no  (root ⊨̷α)
does_⊩_ {l} (branch ts) α with does l ⊨ α
...                       | no  ⊨̷α = no (root ⊨̷α)
...                       | yes ⊨α with doesevery ts ⊩ α
...                                | yes ts⊩α = yes (branch ⊨α ts⊩α)
...                                | no  ts⊩̷α = no  (branch ts⊩̷α)



monotone⊩ : ∀ α → Monotone (_⊩ α)
monotone⊩ α t .t root t⊩α = t⊩α
monotone⊩ α (branch ts) t′ (branch t∈ts t≼t′) (branch _ ts⊩α)
    = monotone⊩ α _ t′ t≼t′ (∈All ts⊩α t∈ts)
  where
    ∈All : {A : Set} {P : A → Set} {x : A} {xs : List A}
           → All P xs → x ∈ xs → P x
    ∈All (Px ∷ Pxs) [ refl ]    = Px
    ∈All (_  ∷ Pxs) (_ ∷ x∈xxs) = ∈All Pxs x∈xxs


--⊨̷→¬⊨ : ∀{l α} → l ⊨̷ α → ¬(l ⊨ α)
--⊨̷→¬⊨ (atom x∉l) (atom x∈l) = x∉l x∈l
--⊨̷→¬⊨ (⊨α ⇒ ⊨̷β) (α ∣⇒ ⊨β) = ⊨̷→¬⊨ ⊨̷β ⊨β
--⊨̷→¬⊨ (⊨α ⇒ ⊨̷β) (⊨̷α ⇒∣ β) = ⊨̷→¬⊨ ⊨̷α ⊨α
--
--¬⊨→⊨̷ : ∀{l α} → ¬(l ⊨ α) → l ⊨̷ α
--
--_⊨%_ : (l : List X) → (α : Formula) → Dec (l ⊨ α)
--l ⊨% atom x  with decide∈ _≟_ x l
--...          | yes x∈l = yes (atom x∈l)
--...          | no  x∉l = no  (⊨̷→¬⊨ (atom x∉l))
--l ⊨% (α ⇒ β) with l ⊨% α | l ⊨% β
--...          | _      | yes ⊨β = yes (α ∣⇒ ⊨β)
--...          | no ¬⊨α | _      = yes (¬⊨→⊨̷ ¬⊨α ⇒∣ β)
--...          | yes ⊨α | no ¬⊨β = no (⊨̷→¬⊨ (⊨α ⇒ ¬⊨→⊨̷ ¬⊨β))
--
--¬⊨→⊨̷ {l} {atom x} ¬⊨α = atom λ x∈l → ¬⊨α (atom x∈l)
--¬⊨→⊨̷ {l} {α ⇒ β}  ¬⊨α with l ⊨% α ⇒ β
--...                   | yes ⊨α⇒β = {!   !} ⇒ ¬⊨→⊨̷ (λ ⊨β → ¬⊨α (α ∣⇒ ⊨β))
--...                   | no ¬⊨α⇒β = {!   !} ⇒ ¬⊨→⊨̷ (λ ⊨β → ¬⊨α (α ∣⇒ ⊨β))
--
--⊨⇒to→ : ∀{l α β} → l ⊨ α ⇒ β → l ⊨ α → l ⊨ β
--⊨⇒to→ (α ∣⇒ ⊨β) ⊨α = ⊨β
--⊨⇒to→ (⊨̷α ⇒∣ β) ⊨α = ⊥-elim (⊨̷→¬⊨ ⊨̷α ⊨α)


atom-rule : ∀{l} {t : Tree l} → ∀ x → x ∈ l → t ⊩ atom x
atom-rule {l} {leaf} x x∈l = leaf (atom x∈l)
atom-rule {l} {branch x₁} x x∈l = branch (atom x∈l) (fAll λ { (s , t) r → atom-rule x {!  monotone⊨!} })

arrow-rule : ∀{α β l} {t : Tree l} → (∀ t′ → t ≼ t′ → t′ ⊩ α → t′ ⊩ β) → t ⊩ α ⇒ β
