{-# OPTIONS --without-K #-}

open import hott.univalence.core

module hott.univalence.properties (univalence : ∀ {i} → Univalence i) where

open import sum
open import equality.core
open import function.isomorphism.core
open import hott.equivalence.core

module _ {i} {X Y : Set i} where
  uni-equiv : (X ≡ Y) ≈ (X ≈ Y)
  uni-equiv = ≡⇒≈ , univalence

  uni-iso : (X ≡ Y) ≅ (X ≈ Y)
  uni-iso = ≈⇒≅ uni-equiv
  open _≅_ uni-iso public using ()
    renaming (from to ≈⇒≡)

  uni-coherence : (f : X ≈ Y) → coerce (≈⇒≡ f) ≡ proj₁ f
  uni-coherence f = ap proj₁ (_≅_.iso₂ uni-iso f)
