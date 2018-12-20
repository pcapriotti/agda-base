module algebra.group.core where

open import level
open import algebra.monoid.core
open import equality.core
open import function.isomorphism
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

module _ {i} {G : Set i} ⦃ grp : IsGroup G ⦄ where
  open IsGroup ⦃ ... ⦄

  left-translation-iso : (g : G) → G ≅ G
  left-translation-iso g = record
    { to = λ x → g * x
    ; from = λ x → inv g * x
    ; iso₁ = λ x → sym (assoc _ _ _)
           · ap (λ u → u * x) (linv g)
           · lunit x
    ; iso₂ = λ x → sym (assoc _ _ _)
           · ap (λ u → u * x) (rinv g)
           · lunit x }

  right-translation-iso : (g : G) → G ≅ G
  right-translation-iso g = record
    { to = λ x → x * g
    ; from = λ x → x * inv g
    ; iso₁ = λ x → assoc _ _ _
           · ap (λ u → x * u) (rinv g)
           · runit x
    ; iso₂ = λ x → assoc _ _ _
           · ap (λ u → x * u) (linv g)
           · runit x }
