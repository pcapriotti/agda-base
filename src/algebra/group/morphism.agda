{-# OPTIONS --without-K  #-}
module algebra.group.morphism where

open import level
open import algebra.group.core
open import algebra.monoid.morphism

module _ {i}{j}
         {X : Set i}⦃ sX : IsGroup X ⦄
         {Y : Set j}⦃ sY : IsGroup Y ⦄ where
  open IsGroup ⦃ ... ⦄

  IsGroupMorphism : (X → Y) → Set (i ⊔ j)
  IsGroupMorphism f = IsMonoidMorphism f
