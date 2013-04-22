{-# OPTIONS --without-K #-}

module overloading.hlevel where

open import sum
open import equality.core
open import overloading.core
open import function.isomorphism

bundle-structure-iso : ∀ {i j} {Base : Set i}
                       (Struct : Base → Set j)
                     → Bundle Struct ≅ Σ Base Struct
bundle-structure-iso Struct = record
  { to = λ { (bundle X s) → X , s }
  ; from = λ { (X , s) → bundle X s }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }
