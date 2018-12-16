module algebra.group.core where

open import level
open import algebra.monoid.core
open import equality.core
open import sum

record IsGroup {i} (G : Set i) : Set i where
  field instance mon : IsMonoid G
  open IsMonoid mon public

  field
    inv : G → G
    linv : (x : G) → inv x * x ≡ e
    rinv : (x : G) → x * inv x ≡ e

Group : ∀ i → Set (lsuc i)
Group i = Σ (Set i) IsGroup
