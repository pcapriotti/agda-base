{-# OPTIONS --without-K #-}
module hott.weak-equivalence.alternative where

open import level using (_⊔_)
open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import equality.isomorphisms
open import function
open import function.extensionality
open import function.isomorphism
open import hott.hlevel
open import hott.weak-equivalence
open import hott.coherence

record _≈r_ {i j}(X : Set i)(Y : Set j) : Set (i ⊔ j) where
  constructor equivalence
  field
    f : X → Y
    g : Y → X
    β : (y : Y) → f (g y) ≡ y
    φ : (y : Y)(x : X)(p : f x ≡ y) → g y ≡ x
    ψ : (y : Y)(x : X)(p : f x ≡ y) → cong f (φ y x p) ⊚ p ≡ β y

_≈'_ : ∀ {i j}(X : Set i)(Y : Set j) → Set _
X ≈' Y = Σ (X → Y) λ f
       → Σ (Σ (Y → X) λ g
       → (y : Y) → f (g y) ≡ y ) λ { (g , β)
       → Σ ((y : Y)(x : X)(p : f x ≡ y) → g y ≡ x) λ φ
       → (y : Y)(x : X)(p : f x ≡ y) → cong f (φ y x p) ⊚ p ≡ β y }

alt-weak-equiv-record : ∀ {i j}{X : Set i}{Y : Set j}
                      → (X ≈' Y) ≡ (X ≈r Y)
alt-weak-equiv-record {X = X}{Y = Y} = ≅⇒≡ (record
  { to = λ { (f , (g , h) , (φ , ψ)) → equivalence f g h φ ψ }
  ; from = λ { (equivalence f g β φ ψ) → (f , (g , β) , (φ , ψ)) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl })

alt-weak-equiv-Σ : ∀ {i j}{X : Set i}{Y : Set j}
                 → (X ≈ Y) ≡ (X ≈' Y)
alt-weak-equiv-Σ {X = X}{Y = Y} =
  cong (Σ (X → Y)) (ext λ f → begin
      weak-equiv f
    ≡⟨ ΠΣ-swap ⟩
      Σ ((y : Y) → f ⁻¹ y) (λ { gβ
      → (y : Y)(x : f ⁻¹ y) → gβ y ≡ x })
    ≡⟨ ≅⇒≡ (Σ-cong-iso ΠΣ-swap-iso (λ _ → refl≅ refl)) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
      → (y : Y)(x : f ⁻¹ y) → (g y , β y) ≡ x } )
    ≡⟨ cong (Σ _) ( ext λ { (g , β)
                  → Π-cong λ y
                  → ≅⇒≡ ( curry-iso (λ x p
                        → (g y , β y) ≡ (x , p))) }) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
      → (y : Y)(x : X)(p : f x ≡ y) → (g y , β y) ≡ (x , p) } )
    ≡⟨ cong (Σ _) ( ext λ { (g , β)
                  → Π-cong λ y → Π-cong λ x → Π-cong λ p
                  → sym (Σ-split {b = β y}{b' = p}) }) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
      → (y : Y)(x : X)(p : f x ≡ y) → Σ (g y ≡ x) λ q
            → subst (λ x → f x ≡ y) q (β y) ≡ p } )
    ≡⟨ cong (Σ _) ( ext λ { (g , β)
                   → ΠΣ-swap ⊚' Π-cong λ y
                   → ΠΣ-swap ⊚' Π-cong λ x
                   → ΠΣ-swap {Z = λ p q → subst (λ x → f x ≡ y) q (β y) ≡ p} }) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
        → Σ ((y : Y)(x : X) → f x ≡ y → g y ≡ x) λ φ
          → (y : Y)(x : X)(p : f x ≡ y)
            → subst (λ x → f x ≡ y) (φ y x p) (β y) ≡ p } )
    ≡⟨ cong (Σ _) ( ext λ { (g , β) → cong (Σ _) (ext' λ φ
                  → Π-cong λ y → Π-cong λ x → Π-cong λ p
                  → lem f g β φ y x p) } ) ⟩
      ( Σ (Σ (Y → X) λ g
      → (y : Y) → f (g y) ≡ y ) λ { (g , β)
      → Σ ((y : Y)(x : X)(p : f x ≡ y) → g y ≡ x) λ φ
      → (y : Y)(x : X)(p : f x ≡ y) → cong f (φ y x p) ⊚ p ≡ β y } )
    ∎ )
  where
    open ≡-Reasoning

    -- flipped transitivity, to make some proofs easier to read
    _⊚'_ : ∀ {i}{X : Set i}{x y z : X} → y ≡ z → x ≡ y → x ≡ z
    p ⊚' q = q ⊚ p

    lem : (f : X → Y)(g : Y → X)(β : (y : Y) → f (g y) ≡ y)
          (φ : (y : Y)(x : X) → f x ≡ y → g y ≡ x)
        → (y : Y)(x : X)(p : f x ≡ y)
        → (subst (λ x → f x ≡ y) (φ y x p) (β y) ≡ p)
        ≡ (cong f (φ y x p) ⊚ p ≡ β y)
    lem f g β φ y x p = cong (λ z → z ≡ p)
      ( subst-naturality (λ x → x ≡ y) f (φ y x p) (β y)
      ⊚ subst-eq (cong f (φ y x p)) (β y) )
      ⊚ sym (move-≡ (cong f (φ y x p)) p (β y))

alt-weak-equiv : ∀ {i j}{X : Set i}{Y : Set j}
               → (X ≈ Y) ≡ (X ≈r Y)
alt-weak-equiv = alt-weak-equiv-Σ ⊚ alt-weak-equiv-record
