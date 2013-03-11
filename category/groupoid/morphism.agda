{-# OPTIONS --without-K #-}

module category.groupoid.morphism where

open import category.groupoid.core
open import category.functor.core

-- a morphism of groupoids is just a functor of the underlying categories
Morphism : ∀ {i j i' j'} (G : Groupoid i j)(H : Groupoid i' j') → Set _
Morphism G H = Functor (cat G) (cat H)
