{-# OPTIONS --without-K #-}

module algebra.monoid.morphism where

open import level
open import equality.core
open import category.category
open import algebra.monoid.core
open import sets.unit
import category.graph as Graph
import category.functor.core as F

Morphism : ∀ {i j} → Monoid i → Monoid j → Set _
Morphism M N = F.Functor (cat M) (cat N)

Id : ∀ {i} → (M : Monoid i) → Morphism M M
Id M = F.Id (cat M)

module Morphism {i j}{M : Monoid i}{N : Monoid j}
                (f : Morphism M N) where
  module Func = F.Functor f
  open mon-interface M
  open mon-interface N

  map : carrier M → carrier N
  map = Func.map

  map-id : map unit ≡ unit
  map-id = Func.map-id tt

  map-hom : ∀ x y → map (x ⋆ y) ≡ map x ⋆ map y
  map-hom = Func.map-hom
