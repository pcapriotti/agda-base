{-# OPTIONS --without-K --type-in-type #-}
module function.isomorphism.univalence where

open import equality.core
open import function.core
open import function.isomorphism.core
open import hott.weak-equivalence.alternative
open import hott.univalence

≅⇒≡ : {X Y : Set} → X ≅ Y → X ≡ Y
≅⇒≡ = ≈⇒≡ ∘ ≅⇒≈
