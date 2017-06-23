{-# OPTIONS --without-K #-}
module hott.equivalence.logical where

open import sum
open import function.isomorphism.core
open import hott.level.core

_↔_ : ∀ {i j} → Set i → Set j → Set _
X ↔ Y = (X → Y) × (Y → X)

module _ {i j}{X : Set i}{Y : Set j} where
  ≅⇒↔ : X ≅ Y → X ↔ Y
  ≅⇒↔ φ = to , from
    where open _≅_ φ

  ↔⇒≅ : h 1 X → h 1 Y → X ↔ Y → X ≅ Y
  ↔⇒≅ hX hY (f , g) = iso f g (λ x → h1⇒prop hX _ x) (λ y → h1⇒prop hY _ y)
