module algebra.monoid.core where

open import level
open import algebra.semigroup
open import equality.core
open import sum

record IsMonoid {i} (M : Set i) : Set i where
  field
    instance sgrp : IsSemigroup M

  open IsSemigroup sgrp public
  field
    e : M
    lunit : (x : M) → e * x ≡ x
    runit : (x : M) → x * e ≡ x

Monoid : ∀ i → Set (lsuc i)
Monoid i = Σ (Set i) IsMonoid
