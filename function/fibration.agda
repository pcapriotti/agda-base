{-# OPTIONS --without-K #-}

module function.fibration where

open import sum
open import equality.core
open import function.core
open import function.isomorphism.core
open import function.isomorphism.utils
open import hott.hlevel.core
open import sets.unit

fib : ∀ {i j}{X : Set i}(Y : X → Set j)
    → Σ X Y → X
fib Y = proj₁

fib-iso : ∀ {i j}{X : Set i}{Y : X → Set j}
        → (x : X)
        → fib Y ⁻¹ x ≅ Y x
fib-iso {X = X}{Y = Y} x = begin
    fib Y ⁻¹ x
  ≅⟨ refl≅ ⟩
    ( Σ (Σ X Y) λ { (x' , y)
    → x' ≡ x } )
  ≅⟨ Σ-assoc-iso ⟩
    ( Σ X λ x' → Y x' × x' ≡ x )
  ≅⟨ (Σ-ap-iso refl≅ λ x' → ×-comm) ⟩
    ( Σ X λ x' → x' ≡ x × Y x' )
  ≅⟨ sym≅ Σ-assoc-iso ⟩
    ( Σ (singleton' x) λ { (x' , _) → Y x' } )
  ≅⟨ Σ-ap-iso' (contr-⊤-iso (singl-contr' x)) (λ _ → refl≅) ⟩
    ( ⊤ × Y x )
  ≅⟨ ×-left-unit ⟩
    Y x
  ∎
  where open ≅-Reasoning

fib-compose : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
            → (f : X → Y)(g : Y → Z)(z : Z)
            → (g ∘' f) ⁻¹ z
            ≅ ( Σ (g ⁻¹ z) λ { (y , _) → f ⁻¹ y } )
fib-compose {X = X}{Y}{Z} f g z = begin
    (g ∘' f) ⁻¹ z
  ≅⟨ refl≅ ⟩
    ( Σ X λ x → g (f x) ≡ z )
  ≅⟨ Σ-ap-iso refl≅ (λ _ → sym≅ ×-left-unit) ⟩
    ( Σ X λ x → ⊤ × g (f x) ≡ z)
  ≅⟨ ( Σ-ap-iso refl≅ λ x
      → Σ-ap-iso (sym≅ (contr-⊤-iso (singl-contr (f x))) ) λ _
      → refl≅ ) ⟩
    ( Σ X λ x
    → singleton (f x)
    × g (f x) ≡ z )
  ≅⟨ ( Σ-ap-iso refl≅ λ x → Σ-assoc-iso ) ⟩
    ( Σ X λ x
    → Σ Y λ y
    → (f x ≡ y)
    × (g (f x) ≡ z) )
  ≅⟨ ( Σ-ap-iso refl≅ λ x
       → Σ-ap-iso refl≅ λ y
       → Σ-ap-iso refl≅ λ p
       → ≡⇒≅ (ap (λ u → g u ≡ z) p) ) ⟩
    ( Σ X λ x
    → Σ Y λ y
    → (f x ≡ y)
    × (g y ≡ z) )
  ≅⟨ Σ-comm-iso ⟩
    ( Σ Y λ y
    → Σ X λ x
    → (f x ≡ y)
    × (g y ≡ z) )
  ≅⟨ ( Σ-ap-iso refl≅ λ y → sym≅ Σ-assoc-iso ) ⟩
    ( Σ Y λ y → (f ⁻¹ y) × (g y ≡ z) )
  ≅⟨ ( Σ-ap-iso refl≅ λ y → ×-comm ) ⟩
    ( Σ Y λ y →  (g y ≡ z) × (f ⁻¹ y) )
  ≅⟨ sym≅ Σ-assoc-iso ⟩
    ( Σ (g ⁻¹ z) λ { (y , _) → f ⁻¹ y } )
  ∎
  where open ≅-Reasoning
