{-# OPTIONS --without-K #-}
module hott.weak-equivalence where

open import equality.core
open import function
open import function.isomorphism
open import function.extensionality.proof-dep
open import hott.univalence

import hott.weak-equivalence.alternative as Alt

open Alt ext' public
open import hott.weak-equivalence.core public

≅⇒≡ : ∀ {i}{X Y : Set i}
     → X ≅ Y → X ≡ Y
≅⇒≡ = ≈⇒≡ ∘ ≅⇒≈
