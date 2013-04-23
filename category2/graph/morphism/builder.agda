{-# OPTIONS --without-K #-}

module category2.graph.morphism.builder where

open import level
open import category2.graph.core

record MorphismBuilder {i j i' j'} (W : Graph i j)
                                   (U : Graph i' j')
                                 : Set (i ⊔ j ⊔ i' ⊔ j') where
  open as-graph W
  open as-graph U
  field
    apply : obj W → obj U
    map : {x y : obj W} → hom x y → hom (apply x) (apply y)
