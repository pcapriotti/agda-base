{-# OPTIONS --without-K #-}

module algebra.monoid.morphism where

open import level
open import equality.core
open import algebra.monoid.core
open import sets.unit
import category.graph as Graph
import category.functor.core as F

Morphism : ∀ {i j} → Monoid i → Monoid j → Set _
Morphism M N = F.Functor (as-category M) (as-category N)

Id : ∀ {i} → (M : Monoid i) → Morphism M M
Id M = F.Id (as-category M)

open F public using (_∘_)

module Morphism {i j}{M : Monoid i}{N : Monoid j}
                (f : Morphism M N) where
  module Func = F.Functor f

  map : carrier M → carrier N
  map = Func.map

  map-id : map unit ≡ unit
  map-id = Func.map-id tt

  map-hom : ∀ x y → map (x ⋆ y) ≡ map x ⋆ map y
  map-hom = Func.map-hom
