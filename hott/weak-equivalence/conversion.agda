{-# OPTIONS --without-K #-}

module hott.weak-equivalence.conversion where

open import equality.core
open import function.core
open import function.isomorphism
open import hott.weak-equivalence.alternative
open import hott.univalence

≅⇒≡ : ∀ {i}{X Y : Set i}
     → X ≅ Y → X ≡ Y
≅⇒≡ = ≈⇒≡ ∘ ≅⇒≈
