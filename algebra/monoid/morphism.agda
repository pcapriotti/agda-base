{-# OPTIONS --without-K #-}

module algebra.monoid.morphism where

open import level
open import algebra.monoid.core
import category.graph as Graph
open import category.functor.class

private
  monoid-gmorphism : ∀ {i j} → Monoid i → Monoid j → Set _
  monoid-gmorphism M N = Graph.Morphism (graph M) (graph N)

open Monoid using (is-mon)

IsMorphism : ∀ {i j}(M : Monoid i)(N : Monoid j)
           → monoid-gmorphism M N → Set _
IsMorphism M N = IsFunctor (is-mon M) (is-mon N)

record Morphism {i j}(M : Monoid i)(N : Monoid j) : Set (i ⊔ j) where
  field
    func : monoid-gmorphism M N
    is-mor : IsMorphism M N func

  open Graph.Morphism func public
  open IsFunctor is-mor public
