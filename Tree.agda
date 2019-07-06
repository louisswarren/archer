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


data _≼_ {A : Set} {l : List A} : Tree l → {m : List A} → Tree m → Set where
  root   : ∀{t} → t ≼ t
  branch : ∀{ts s t m} {t′ : Tree m}
           → (s , t) ∈ ts → t ≼ t′ → (branch ts) ≼ t′

Monotone : {A : Set} → (P : {l : List A} → Tree l → Set) → Set
Monotone P = ∀{l m} → (t : Tree l) → (t′ : Tree m) → t ≼ t′ → P t → P t′
