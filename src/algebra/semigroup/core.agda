module algebra.semigroup.core where

open import level
open import equality.core
open import sum

record IsSemigroup {i} (X : Set i) : Set i where
  field
    _*_ : X → X → X
    assoc : (x y z : X) → x * (y * z) ≡ (x * y) * z

Semigroup : ∀ i → Set (lsuc i)
Semigroup i = Σ (Set i) IsSemigroup
