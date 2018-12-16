module algebra.monoid.morphism where

open import level
open import algebra.monoid.core
open import algebra.semigroup.morphism
open import equality.core

module _ {i}{j}
         {X : Set i}⦃ sX : IsMonoid X ⦄
         {Y : Set j}⦃ sY : IsMonoid Y ⦄ where
  open IsMonoid ⦃ ... ⦄

  record IsMonoidMorphism (f : X → Y) : Set (i ⊔ j) where
    field
      sgrp-mor : IsSemigroupMorphism f
      id-pres : f e ≡ e
