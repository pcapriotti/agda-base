{-# OPTIONS --without-K #-}

module category2.groupoid.morphism where

open import category2.category
open import category2.groupoid.core
open import category2.functor.core

-- a morphism of groupoids is just a functor of the underlying categories
Morphism : ∀ {i j i' j'} (G : Groupoid i j)(H : Groupoid i' j') → Set _
Morphism G H = Functor (cat G) (cat H)
