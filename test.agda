open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Decidable

instance ℕD : Discrete ℕ
ℕD ⟨ zero  ≟ zero  ⟩ = yes refl
ℕD ⟨ suc x ≟ suc y ⟩ with x ≟ y
...                  | yes refl = yes refl
...                  | no  x≢y  = no  λ { refl → x≢y refl }
ℕD ⟨ zero  ≟ suc _ ⟩ = no λ ()
ℕD ⟨ suc _ ≟ zero  ⟩ = no λ ()

open import Formula ℕ
open import List

fis_∈_ : (x : Formula) → (xs : List Formula) → Dec (x ∈ xs)
fis x ∈ xs = is x ∈ xs
