{-# OPTIONS --without-K #-}

module algebra.monoid.core where

open import level
open import function.core
open import category.graph
  hiding (graph)
open import category.class
open import sets.unit

private
  monoid-graph : ∀ {i} → Set i → Graph lzero i
  monoid-graph X = record
    { obj = ⊤
    ; hom = λ _ _ → X }

IsMonoid : ∀ {i} → Set i → Set i
IsMonoid X = IsCategory (monoid-graph X)

record Monoid i : Set (lsuc i) where
  field
    carrier : Set i
    is-mon : IsMonoid carrier

open Monoid public

graph : ∀ {i} → Monoid i → Graph lzero i
graph M = monoid-graph (carrier M)
