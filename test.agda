open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List

open import Decidable
open import Ensemble

natEq : Decidable≡ ℕ
natEq zero    zero    = yes refl
natEq zero    (suc m) = no λ ()
natEq (suc n) zero    = no λ ()
natEq (suc n) (suc m) with natEq n m
...                   | yes refl = yes refl
...                   | no  n≢m  = no  λ { refl → n≢m refl }

open import Logic ℕ natEq


α β γ : Formula
α = atom 1
β = atom 2
γ = atom 3

n = reduce ∅ (α ⇒ β ⇒ γ) from∅
δ = fst n
x = fst (snd n)
