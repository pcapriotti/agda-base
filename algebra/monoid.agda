{-# OPTIONS --without-K #-}

module algebra.monoid where

open import level
open import category.graph
open import category.class
open import sets.unit

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
