{-# OPTIONS --without-K  #-}
module algebra.semigroup.core where

open import level
open import equality.core
open import sum
open import hott.level

record IsSemigroup {i} (X : Set i) : Set i where
  field
    _*_ : X → X → X
    assoc : (x y z : X) → (x * y) * z ≡ x * (y * z)

    is-set : h 2 X

Semigroup : ∀ i → Set (lsuc i)
Semigroup i = Σ (Set i) IsSemigroup
