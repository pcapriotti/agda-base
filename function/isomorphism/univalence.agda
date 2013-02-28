{-# OPTIONS --without-K #-}
module function.isomorphism.univalence where

open import equality.core
open import function.core
open import function.isomorphism.core
open import hott.weak-equivalence.alternative
open import hott.univalence

≅⇒≡ : ∀ {i}{X Y : Set i}
     → X ≅ Y → X ≡ Y
≅⇒≡ = ≈⇒≡ ∘ ≅⇒≈
