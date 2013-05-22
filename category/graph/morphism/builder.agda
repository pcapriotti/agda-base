{-# OPTIONS --without-K --type-in-type #-}

module category.graph.morphism.builder where

open import level
open import category.graph.core

record MorphismBuilder (W U : Graph) : Set where
  open as-graph W
  open as-graph U
  field
    apply : obj W → obj U
    map : {x y : obj W} → hom x y → hom (apply x) (apply y)
