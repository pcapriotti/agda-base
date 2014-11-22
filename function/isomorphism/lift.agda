{-# OPTIONS --without-K #-}
module function.isomorphism.lift where

open import level
open import equality
open import function.isomorphism.core

-- lifting is an isomorphism
lift-iso : ∀ {i} j (X : Set i) → X ≅ ↑ j X
lift-iso j X = iso lift lower (λ _ → refl) (λ _ → refl)
