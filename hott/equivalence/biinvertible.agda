{-# OPTIONS --without-K #-}
module hott.equivalence.biinvertible where

open import sum
open import equality
open import function.core
open import function.isomorphism.core
open import function.isomorphism.utils
open import function.overloading
open import function.extensionality
open import hott.level.core
open import hott.level.closure
open import hott.equivalence.core
open import hott.equivalence.alternative
open import sets.unit

module _ {i j}{X : Set i}{Y : Set j} where
  InvL : (X → Y) → Set _
  InvL f = Σ (Y → X) λ g → (x : X) → g (f x) ≡ x

  InvR : (X → Y) → Set _
  InvR f = Σ (Y → X) λ g → (y : Y) → f (g y) ≡ y

  BiInv : (X → Y) → Set _
  BiInv f = InvL f × InvR f

_≈₂_ : ∀ {i j} → Set i → Set j → Set _
X ≈₂ Y = Σ (X → Y) BiInv

module _ {i j}{X : Set i}{Y : Set j} where
  ≅⇒b : X ≅ Y → X ≈₂ Y
  ≅⇒b f = apply f , (invert f , _≅_.iso₁ f) , (invert f , _≅_.iso₂ f)

  b⇒≅ : X ≈₂ Y → X ≅ Y
  b⇒≅ (f , (g , α) , (h , β)) = record
    { to = f
    ; from = g
    ; iso₁ = α
    ; iso₂ = λ y → sym (ap (f ∘' g) (β y)) · ap f (α (h y)) · β y }

  module _ (isom : X ≅ Y) where
    private
      f : X → Y
      f = apply isom

      φ : ∀ {k} (Z : Set k) → (X → Z) ≅ (Y → Z)
      φ Z = record
        { to = λ u → u ∘ invert isom
        ; from = λ v → v ∘ f
        ; iso₁ = λ u → funext λ x → ap u (_≅_.iso₁ isom x)
        ; iso₂ = λ v → funext λ y → ap v (_≅_.iso₂ isom y) }

    invl-level : contr (InvL f)
    invl-level = iso-level (Σ-ap-iso refl≅ λ g → sym≅ strong-funext-iso)
                           (proj₂ (≅⇒≈ (sym≅ (φ X))) id)

    private
      ψ : ∀ {k} (Z : Set k) → (Z → X) ≅ (Z → Y)
      ψ Z = record
        { to = λ u → f ∘ u
        ; from = λ v → invert isom ∘ v
        ; iso₁ = λ u → funext λ x → _≅_.iso₁ isom (u x)
        ; iso₂ = λ v → funext λ y → _≅_.iso₂ isom (v y) }

    invr-level : contr (InvR f)
    invr-level = iso-level (Σ-ap-iso refl≅ λ h → sym≅ strong-funext-iso)
                           (proj₂ (≅⇒≈ (ψ Y)) id)

  BiInv-level : (f : X → Y) → h 1 (BiInv f)
  BiInv-level f b₁ b₂ = h↑ (×-contr (invl-level isom) (invr-level isom)) b₁ b₂
    where
      isom : X ≅ Y
      isom = b⇒≅ (f , b₁)

  b⇔≈ : (X ≈₂ Y) ≅ (X ≈ Y)
  b⇔≈ = record
    { to = λ b → ≅⇒≈ (b⇒≅ b)
    ; from = λ φ → (≅⇒b (≈⇒≅ φ))
    ; iso₁ = λ { (f , b) → ap (λ b → f , b) (h1⇒prop (BiInv-level f) _ _) }
    ; iso₂ = λ { (f , e) → ap (λ e → f , e) (h1⇒prop (weak-equiv-h1 f) _ _) } }
