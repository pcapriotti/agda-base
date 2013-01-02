{-# OPTIONS --without-K #-}
module function.isomorphism.properties where

open import level
open import sum
open import sets.nat
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.isomorphism
open import function.isomorphism.coherent
open import hott.hlevel

-- lifting is an isomorphism
lift-iso : ∀ {i} j (X : Set i) → X ≅ ↑ j X
lift-iso j X = iso lift lower (λ _ → refl) (λ _ → refl)
