module Tree where

open import Agda.Builtin.Sigma

open import List

data Tree {A : Set} (l : List A) : Set

Subtree : {A : Set} → List A → Set
Subtree {A} l = Σ (List A) λ s → Tree (s ++ l)

data Tree {A} l where
  leaf   : Tree l
  branch : List (Subtree l) → Tree l

