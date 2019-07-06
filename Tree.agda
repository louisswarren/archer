module Tree where

open import Agda.Builtin.Sigma

open import List

data Tree {A : Set} (l : List A) : Set

Subtree : {A : Set} → List A → Set
Subtree {A} l = Σ (List A) λ s → Tree (s ++ l)

-- Turn a predicate on subtrees into a predicate on trees
_∘lop : {A : Set} {l : List A}
      → (P : {m : List A} → Tree m → Set) → Subtree l → Set
P ∘lop = λ { (s , t) → P t }

data Tree {A} l where
  leaf   : Tree l
  branch : List (Subtree l) → Tree l

data AllTree {A : Set} (P : List A → Set) {l : List A} : Tree l → Set where
  leaf   : P l → AllTree P leaf
  branch : ∀{ts} → P l → All (AllTree P ∘lop) ts → AllTree P (branch ts)

data AnyTree {A : Set} (P : List A → Set) {l : List A} : Tree l → Set where
  root   : ∀{t} → P l → AnyTree P t
  branch : ∀{ts} → Any (AnyTree P ∘lop) ts → AnyTree P (branch ts)
