open import Decidable
open import List using (List ; [] ; _∷_)

Ensemble : Set → Set₁
Ensemble A = A → Set

infix 4 _∈_ _∉_

_∈_ : {A : Set} → A → Ensemble A → Set
α ∈ αs = αs α

_∉_ : {A : Set} → A → Ensemble A → Set
α ∉ αs = ¬(α ∈ αs)

infix 4 _⊂_
_⊂_ : {A : Set} → Ensemble A → Ensemble A → Set
αs ⊂ βs = ∀ x → x ∈ αs → ¬(x ∉ βs)


∅ : {A : Set} → Ensemble A
∅ = λ _ → ⊥

⟨_⟩ : {A : Set} → A → Ensemble A
⟨ α ⟩ = λ x → x ≡ α

infixr 5 _∪_
_∪_ : {A : Set} → Ensemble A → Ensemble A → Ensemble A
(αs ∪ βs) = λ x → x ∉ αs → ¬(x ∉ βs)

infixl 5 _-_
_-_ : {A : Set} → Ensemble A → A → Ensemble A
(αs - α) = λ x → ¬(x ≢ α → x ∉ αs)


data Assembled {A : Set} (eq : Decidable≡ A) : Pred A → Set₁ where
  from∅   : Assembled eq ∅
  from⟨_⟩ : (α : A)  → Assembled eq (⟨ α ⟩)
  from_∪_ : ∀{αs βs} → Assembled eq αs → Assembled eq βs
                       → Assembled eq (αs ∪ βs)
  from_-_ : ∀{αs}    → Assembled eq αs → (α : A) → Assembled eq (αs - α)


decide∈ : {A : Set} {eq : Decidable≡ A} {αs : Ensemble A}
          → (x : A) → Assembled eq αs → Dec (x ∈ αs)
decide∈          x from∅            = no λ x∈∅ → x∈∅
decide∈ {_} {eq} x (from⟨ α ⟩)      = eq x α
decide∈          x (from Aαs ∪ Aβs) with decide∈ x Aαs
...   | yes x∈αs = yes λ x∉αs _ → x∉αs x∈αs
...   | no  x∉αs with decide∈ x Aβs
...              | yes x∈βs = yes λ _ x∉βs → x∉βs x∈βs
...              | no  x∉βs = no  λ x∉αs∪βs → x∉αs∪βs x∉αs x∉βs
decide∈ {_} {eq} x (from Aαs - α)   with eq x α
...   | yes refl = no λ α∈αs-α → α∈αs-α λ α≢α _ → α≢α refl
...   | no x≢α   with decide∈ x Aαs
...              | yes x∈αs = yes λ x≢α→x∉αs → x≢α→x∉αs x≢α x∈αs
...              | no  x∉αs = no  λ x∈αs-α
                                    → x∈αs-α (λ _ _
                                              → x∈αs-α (λ _ _
                                                        → x∈αs-α (λ _
                                                                  → x∉αs)))


infixr 5 _all∪_

data All_[_∖_] {A : Set} (P : Pred A) : Ensemble A → List A → Set₁ where
  all∅    : ∀{xs}       → All P [ ∅ ∖ xs ]
  all⟨_⟩  : ∀{α xs}     → P α         → All P [ ⟨ α ⟩ ∖ xs ]
  all⟨-_⟩ : ∀{α xs}     → α List.∈ xs → All P [ ⟨ α ⟩ ∖ xs ]
  _all∪_  : ∀{αs βs xs} → All P [ αs ∖ xs ] → All P [ βs ∖ xs ]
                          → All P [ αs ∪ βs ∖ xs ]
  all-_   : ∀{αs x xs}  → All P [ αs ∖ x ∷ xs ] → All P [ αs - x ∖ xs ]


All : {A : Set} → Pred A → Ensemble A → Set₁
All P αs = All P [ αs ∖ [] ]


stable∈ : {A : Set} {Γ : Ensemble A} → (eq : Decidable≡ A) → Assembled eq Γ → ∀ x → ¬(x ∉ Γ) → x ∈ Γ
stable∈ eq from∅ x ¬x∉Γ = ¬x∉Γ (λ z → z)
stable∈ eq from⟨ y ⟩ x ¬x∉Γ with eq x y
...                         | yes refl = refl
...                         | no x≢y = ⊥-elim (¬x∉Γ x≢y)
stable∈ eq (from αs ∪ βs) x ¬x∉Γ = λ z z₁ → z₁ (stable∈ eq βs x (λ z₂ → ¬x∉Γ (λ z₃ → z₃ z z₂)))
stable∈ eq (from αs - y)  x ¬x∉Γ = λ z →   z (λ z₁ → ¬x∉Γ (λ z₂ → z₂ (λ z₃ _ → z₃ z₁)))   (stable∈ eq αs x (λ z₁ → ¬x∉Γ (λ z₂ → z₂ (λ _ → z₁))))


