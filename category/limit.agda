{-# OPTIONS --without-K #-}

open import level
open import category.category
open import category.functor
open import category.kan-extension
open import category.instances.unit
open import sets.unit

module category.limit {i}{j}{i'}{j'}
  (C : Category i j)(J : Category i' j') where

open Category
open Functor

Cone : Functor J C → Set _
Cone D = Extension (unit-func J) D

record Lim (D : Functor J C) : Set (i ⊔ j ⊔ i' ⊔ j') where
  field ext : Ran (unit-func J) D

  open Ran _ _ ext public hiding (ext)
    renaming ( counit to cone
             ; ext-univ to cone-univ )

  X : obj C
  X = apply F tt
