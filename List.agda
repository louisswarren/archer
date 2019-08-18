module List where

open import Agda.Builtin.List public

open import Decidable

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

++assoc : {A : Set} → (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++assoc []       ys zs = refl
++assoc (x ∷ xs) ys zs rewrite ++assoc xs ys zs = refl


infix 4 _∈_ _∉_

data _∈_ {A : Set} (x : A) : List A → Set where
  [] : ∀{xs} → x ∈ (x ∷ xs)
  _∷_ : ∀{xs} → (y : A) → x ∈ xs → x ∈ (y ∷ xs)

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = ¬(x ∈ xs)


after : {A : Set} {ys : List A} → ∀ x xs → x ∈ (xs ++ x ∷ ys)
after x []       = []
after x (y ∷ xs) = y ∷ after x xs

later : {A : Set} {x : A} {xs : List A} → ∀ ys → x ∈ xs → x ∈ ys ++ xs
later [] x∈xs = x∈xs
later (y ∷ ys) x∈xs = y ∷ later ys x∈xs

is_∈_ : {A : Set} ⦃ _ : Discrete A ⦄ → (x : A) → (xs : List A) → Dec (x ∈ xs)
is x ∈ []       = no λ ()
is x ∈ (y ∷ xs) with x ≟ y
...             | yes refl = yes []
...             | no  x≢y  with is x ∈ xs
...                        | yes x∈xs = yes (y ∷ x∈xs)
...                        | no  x∉xs = no  λ { []         → x≢y refl
                                              ; (_ ∷ x∈xs) → x∉xs x∈xs }

∀[_]_ : {A : Set} → List A → Pred A → Set
∀[ xs ] P = ∀{x} → x ∈ xs → P x

is∀[_] : {A : Set} {P : Pred A} → (xs : List A) → Decidable P → Dec (∀[ xs ] P)
is∀[ [] ]     p = yes λ {x} ()
is∀[ x ∷ xs ] p with p x
...             | no ¬Px = no λ z → ¬Px (z [])
...             | yes Px with is∀[ xs ] p
...                      | yes ∀xsP = yes λ { [] → Px; (y ∷ k) → ∀xsP k }
...                      | no ¬∀xsP = no  λ z → ¬∀xsP (λ {x} z₁ → z (_ ∷ z₁))

--data All {A : Set} (P : Pred A) : List A → Set
--syntax All P xs = ∀[ xs ] P
--data All {A} P where
--  []  : ∀[ [] ] P
--  _∷_ : ∀{x xs} → P x → ∀[ xs ] P → ∀[ x ∷ xs ] P
--
--is∀[_] : {A : Set} {P : Pred A} → (xs : List A) → Decidable P → Dec (∀[ xs ] P)
--is∀[ [] ]     p = yes []
--is∀[ x ∷ xs ] p with p x
--...             | no ¬Px = no λ { (Px ∷ _) → ¬Px Px }
--...             | yes Px with is∀[ xs ] p
--...                      | yes ∀xsP = yes (Px ∷ ∀xsP)
--...                      | no ¬∀xsP = no  λ { (_ ∷ ∀xsP) → ¬∀xsP ∀xsP }
