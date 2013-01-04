{-# OPTIONS --without-K #-}
module hott.weak-equivalence where

open import equality.core
open import function.core
open import function.isomorphism
open import function.extensionality.dependent
open import hott.univalence

open import hott.weak-equivalence.alternative public
open import hott.weak-equivalence.core public

≅⇒≡ : ∀ {i}{X Y : Set i}
     → X ≅ Y → X ≡ Y
≅⇒≡ = ≈⇒≡ ∘ ≅⇒≈
