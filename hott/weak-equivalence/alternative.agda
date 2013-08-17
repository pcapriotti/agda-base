{-# OPTIONS --without-K #-}
open import function.extensionality.core

module hott.weak-equivalence.alternative where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.extensionality.proof
open import function.isomorphism.core
open import function.isomorphism.coherent
open import function.isomorphism.utils
open import hott.hlevel.core
open import hott.weak-equivalence.core
open import hott.univalence

module _ {i j}{X : Set i}{Y : Set j} where
  open ≅-Reasoning

  private
    we-split-iso : (f : X → Y) → _
    we-split-iso f = begin
        weak-equiv f
      ≅⟨ ΠΣ-swap-iso ⟩
        ( Σ ((y : Y) → f ⁻¹ y) λ gβ
        → (y : Y)(u : f ⁻¹ y) → gβ y ≡ u )
      ≅⟨ Σ-ap-iso₁ ΠΣ-swap-iso ⟩
        ( Σ (Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y) λ { (g , β)
        → (y : Y)(u : f ⁻¹ y) → (g y , β y) ≡ u } )
      ≅⟨ Σ-assoc-iso ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → (y : Y)(u : f ⁻¹ y) → (g y , β y) ≡ u )
      ≅⟨ ( Σ-ap-iso₂ λ g
         → Σ-ap-iso₂ λ β
         → Π-ap-iso refl≅ λ y
         → curry-iso (λ x p → (g y , β y) ≡ (x , p)) ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → (y : Y)(x : X)(p : f x ≡ y)
        → (g y , β y) ≡ (x , p) )
      ≅⟨ ( Σ-ap-iso₂ λ g
          → Σ-ap-iso₂ λ β
          → Π-ap-iso refl≅ λ y
          → Π-ap-iso refl≅ λ x
          → Π-ap-iso refl≅ λ p
          → sym≅ Σ-split-iso ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → (y : Y)(x : X)(p : f x ≡ y)
        → Σ (g y ≡ x) λ q
        → subst (λ x' → f x' ≡ y) q (β y) ≡ p )
      ≅⟨ ( Σ-ap-iso₂ λ g
          → Σ-ap-iso₂ λ β
          → Π-ap-iso refl≅ λ y
          → Π-ap-iso refl≅ λ x
          → Π-ap-iso refl≅ λ p
          → Σ-ap-iso₂ λ q
          → trans≡-iso (
                 subst-naturality (λ x' → x' ≡ y) f q (β y)
               · subst-eq (ap f q) (β y)) ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → (y : Y)(x : X)(p : f x ≡ y)
        → Σ (g y ≡ x) λ q
        → sym (ap f q) · β y ≡ p )
      ≅⟨ ( Σ-ap-iso₂ λ g
          → Σ-ap-iso₂ λ β
          → Π-comm-iso ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → (x : X)(y : Y)(p : f x ≡ y)
        → Σ (g y ≡ x) λ q
        → sym (ap f q) · β y ≡ p )
      ≅⟨ ( Σ-ap-iso₂ λ g
         → Σ-ap-iso₂ λ β
         → Π-ap-iso refl≅ λ x
         → sym≅ J-iso ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → (x : X)
        → Σ (g (f x) ≡ x) λ q
        → sym (ap f q) · β (f x) ≡ refl )
      ≅⟨ ( Σ-ap-iso₂ λ g
         → Σ-ap-iso₂ λ β
         → ΠΣ-swap-iso ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → Σ ((x : X) → g (f x) ≡ x) λ α
        → (x : X) → sym (ap f (α x)) · β (f x) ≡ refl )
      ≅⟨ ( Σ-ap-iso₂ λ g
         → Σ-ap-iso₂ λ β
         → Σ-ap-iso₂ λ α
         → Π-ap-iso refl≅ λ x
         → (trans≅ (sym≅ (move-≡-iso (ap f (α x)) refl (β (f x))))
                    (trans≡-iso (left-unit (ap f (α x))))) ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → Σ ((x : X) → g (f x) ≡ x) λ α
        → (x : X) → ap f (α x) ≡ β (f x) )
      ≅⟨ ( Σ-ap-iso₂ λ g → Σ-comm-iso ) ⟩
        ( Σ (Y → X) λ g
        → Σ ((x : X) → g (f x) ≡ x) λ α
        → Σ ((y : Y) → f (g y) ≡ y) λ β
        → ((x : X) → ap f (α x) ≡ β (f x)) )
      ∎

  ≈⇔≅' : (X ≈ Y) ≅ (X ≅' Y)
  ≈⇔≅' = begin
      (X ≈ Y)
    ≅⟨ Σ-ap-iso₂ we-split-iso ⟩
      ( Σ (X → Y) λ f
      → Σ (Y → X) λ g
      → Σ ((x : X) → g (f x) ≡ x) λ α
      → Σ ((y : Y) → f (g y) ≡ y) λ β
      → ((x : X) → ap f (α x) ≡ β (f x)) )
    ≅⟨ record
         { to = λ {(f , g , α , β , γ) → iso f g α β , γ }
         ; from = λ { (iso f g α β , γ) → f , g , α , β , γ }
         ; iso₁ = λ _ → refl
         ; iso₂ = λ _ → refl } ⟩
      (X ≅' Y)
    ∎

  open _≅_ ≈⇔≅' public using ()
    renaming ( to to ≈⇒≅'
             ; from to ≅'⇒≈ )

  ≅⇒≈ : (X ≅ Y) → (X ≈ Y)
  ≅⇒≈ = ≅'⇒≈ ∘ ≅⇒≅'
