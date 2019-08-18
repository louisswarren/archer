module Tree where

open import Agda.Builtin.Sigma

open import List

data Tree {A : Set} (l : List A) : Set

record Subtree {A : Set} (l : List A) : Set where
  constructor subtree
  inductive
  field
    ext  : List A
    tree : Tree (ext ++ l)

data Tree {A} l where
  stem : List (Subtree l) → Tree l

pattern leaf = stem []

Labels : {A : Set} {l : List A} → Tree l → List A
Labels {A} {l} t = l

TreePred : Set → Set₁
TreePred A = {l : List A} → Tree l → Set

_∘lop : {A : Set} → TreePred A → {l : List A} → Subtree l → Set
(P ∘lop) (subtree s t) = P t

-- A proof of ≼ is a path within the tree
data _≼_ {A : Set} {l : List A} : Tree l → {m : List A} → Tree m → Set where
  [] : ∀{t} → t ≼ t
  _∷_ : ∀{ts s t m} {t′ : Tree m} → (subtree s t) ∈ ts → t ≼ t′ → (stem ts) ≼ t′

≼trans : {A : Set} {l m n : List A} {t : Tree l} {t′ : Tree m} {t″ : Tree n}
         → t ≼ t′ → t′ ≼ t″ → t ≼ t″
≼trans []            t′≼t″ = t′≼t″
≼trans (t∈ts ∷ t≼t′) t′≼t″ = t∈ts ∷ ≼trans t≼t′ t′≼t″

Labelext : {A : Set} {l m : List A} {t : Tree l} {t′ : Tree m}
           → t ≼ t′ → Σ _ λ s → m ≡ s ++ l
Labelext [] = [] , refl
Labelext (t∈ts ∷ t≼t′) with Labelext t≼t′
Labelext (_∷_ {s = s} _ _) | s′ , refl = s′ ++ s , ++assoc s′ s _


∀[≽_]_ : {A : Set} {l : List A} → Tree l → TreePred A → Set
∀[≽ t ] P = ∀{m} {t′ : Tree m} → t ≼ t′ → P t′

Closed : {A : Set} → TreePred A → Set
Closed P = ∀{l} → (t : Tree l) → P t → ∀[≽ t ] P

-- A tree predicate defined by generalising another tree predicate over the
-- entire tree is closed
ClosedClosed : {A : Set} → (P : TreePred A) → Closed (∀[≽_] P)
ClosedClosed P t ∀[≽t]P t≼t′ t′≼t″ = ∀[≽t]P (≼trans t≼t′ t′≼t″)


-- Labelling is indeed monotone
label-closed : {A : Set} {l m : List A}
                 → (t : Tree l) → (t′ : Tree m)
                 → ∀[≽ t ] λ t′ → ∀ x → x ∈ Labels t → x ∈ Labels t′
label-closed t t′ []            x x∈l = x∈l
label-closed _ t′ (t∈ts ∷ t≼t′) x x∈l = label-closed _ t′ t≼t′ x (later _ x∈l)

