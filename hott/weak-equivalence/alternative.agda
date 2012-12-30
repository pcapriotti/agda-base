{-# OPTIONS --without-K #-}
module hott.weak-equivalence.alternative where

open import level using (_⊔_)
open import sum
open import equality.core
open import equality.calculus
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
                      → (X ≈' Y) ≅ (X ≈r Y)
alt-weak-equiv-record {X = X}{Y = Y} = record
  { to = λ { (f , (g , h) , (φ , ψ)) → equivalence f g h φ ψ }
  ; from = λ { (equivalence f g β φ ψ) → (f , (g , β) , (φ , ψ)) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

alt-weak-equiv-Σ : ∀ {i j}{X : Set i}{Y : Set j}
                 → (X ≈ Y) ≅ (X ≈' Y)
alt-weak-equiv-Σ {X = X}{Y = Y} =
  Σ-cong-iso refl≅ (λ f → begin
      weak-equiv f
    ≅⟨ ΠΣ-swap-iso ⟩
      Σ ((y : Y) → f ⁻¹ y) (λ { gβ
      → (y : Y)(x : f ⁻¹ y) → gβ y ≡ x })
    ≅⟨ Σ-cong-iso ΠΣ-swap-iso (λ _ → refl≅) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
      → (y : Y)(x : f ⁻¹ y) → (g y , β y) ≡ x } )
    ≅⟨ Σ-cong-iso refl≅ (λ { (g , β)
         → Π-iso λ y
         → curry-iso (λ x p → (g y , β y) ≡ (x , p)) }) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
      → (y : Y)(x : X)(p : f x ≡ y) → (g y , β y) ≡ (x , p) } )
    ≅⟨ Σ-cong-iso refl≅ (λ { (g , β)
        → Π-iso λ y → Π-iso λ x → Π-iso λ p
        → sym≅ (Σ-split-iso {b = β y}{b' = p}) }) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
      → (y : Y)(x : X)(p : f x ≡ y) → Σ (g y ≡ x) λ q
            → subst (λ x → f x ≡ y) q (β y) ≡ p } )
    ≅⟨ Σ-cong-iso refl≅ (λ { (g , β)
         → ΠΣ-swap-iso ⋆ Π-iso λ y
         → ΠΣ-swap-iso ⋆ Π-iso λ x
         → ΠΣ-swap-iso {Z = λ p q → subst (λ x → f x ≡ y) q (β y) ≡ p} }) ⟩
      ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
        → Σ ((y : Y)(x : X) → f x ≡ y → g y ≡ x) λ φ
          → (y : Y)(x : X)(p : f x ≡ y)
            → subst (λ x → f x ≡ y) (φ y x p) (β y) ≡ p } )
    ≅⟨ Σ-cong-iso refl≅ (λ { (g , β)
        → Σ-cong-iso refl≅ λ φ
        → Π-iso λ y → Π-iso λ x → Π-iso λ p
        → ≡⇒≅ (lem f g β φ y x p) } ) ⟩
      ( Σ (Σ (Y → X) λ g
      → (y : Y) → f (g y) ≡ y ) λ { (g , β)
      → Σ ((y : Y)(x : X)(p : f x ≡ y) → g y ≡ x) λ φ
      → (y : Y)(x : X)(p : f x ≡ y) → cong f (φ y x p) ⊚ p ≡ β y } )
    ∎ )
  where
    open ≅-Reasoning

    Π-iso : ∀ {i j j'} {X : Set i}
            {Y : X → Set j}{Y' : X → Set j'}
          → ((x : X) → Y x ≅ Y' x)
          → ((x : X) → Y x)
          ≅ ((x : X) → Y' x)
    Π-iso = Π-cong-iso ext' refl≅

    -- flipped transitivity of isomorphism
    -- makes some proofs easier to read
    _⋆_ : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
        → Y ≅ Z → X ≅ Y → X ≅ Z
    isom ⋆ isom' = trans≅ isom' isom

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
               → (X ≈ Y) ≅ (X ≈r Y)
alt-weak-equiv = trans≅ alt-weak-equiv-Σ alt-weak-equiv-record
