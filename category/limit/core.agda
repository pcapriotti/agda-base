{-# OPTIONS --without-K #-}

open import level
open import function.overloading
open import category.category
open import category.graph
open import category.functor
open import category.kan-extension
open import category.instances.unit
open import sets.unit

module category.limit.core {i}{j}{i'}{j'}
  {C : Category i j}{J : Category i' j'} where

Cone : Functor J C → Set _
Cone D = Extension (unit-func J) D

record Lim (D : Functor J C)
  : Set (i' ⊔ j' ⊔ lsuc (lsuc (i ⊔ j))) where
  field ran : Ran (unit-func J) D

  open Ran ran public
    renaming ( counit to cone
             ; ext-univ to cone-univ )

  X : obj C
  X = apply F tt
