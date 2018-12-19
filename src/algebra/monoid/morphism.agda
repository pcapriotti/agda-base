module algebra.monoid.morphism where

open import level
open import algebra.monoid.core
open import algebra.semigroup.morphism
open import equality.core
open import function.isomorphism
open import hott.level
open import sum

module _ {i}{j}
         {X : Set i}⦃ sX : IsMonoid X ⦄
         {Y : Set j}⦃ sY : IsMonoid Y ⦄ where
  open IsMonoid ⦃ ... ⦄

  record IsMonoidMorphism (f : X → Y) : Set (i ⊔ j) where
    constructor mk-is-monoid-morphism
    field
      sgrp-mor : IsSemigroupMorphism f
      id-pres : f e ≡ e

  is-monoid-morphism-struct-iso : (f : X → Y)
    → IsMonoidMorphism f ≅ (IsSemigroupMorphism f × (f e ≡ e))
  is-monoid-morphism-struct-iso f = record
    { to = λ mor → ( IsMonoidMorphism.sgrp-mor mor
                   , IsMonoidMorphism.id-pres mor )
    ; from = λ { (s , i) → mk-is-monoid-morphism s i }
    ; iso₁ = λ _ → refl
    ; iso₂ = λ _ → refl }

  is-monoid-morphism-level : (f : X → Y) → h 1 (IsMonoidMorphism f)
  is-monoid-morphism-level f =
    iso-level (sym≅ (is-monoid-morphism-struct-iso f))
    (×-level (is-semigroup-morphism-level f)
    (is-set _ _))
