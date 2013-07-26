{-# OPTIONS --type-in-type --without-K #-}

open import level
open import function.overloading
open import category.category
open import category.graph
open import category.functor
open import category.kan-extension
open import category.instances.unit
open import sets.unit

module category.limit.core {C J : Category} where

Cone : Functor J C → Set
Cone D = Extension {C' = unit} (unit-func J) D

record Lim (D : Functor J C) : Set  where
  field ran : Ran {C' = unit} (unit-func J) D

  open Ran ran public
    renaming ( counit to cone
             ; ext-univ to cone-univ )

  X : obj C
  X = apply F tt
