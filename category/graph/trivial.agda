{-# OPTIONS --without-K #-}

module category.graph.trivial where

open import level
open import function.core
open import category.graph.core
open import category.graph.morphism
open import sets.unit

trivial-graph : ∀ {i}(X : Set i) → Graph lzero i
trivial-graph X = mk-graph record
  { obj = ⊤
  ; hom = λ _ _ → X }

trivial-morphism : ∀ {i j}{X : Set i}{Y : Set j}
                 → (f : X → Y)
                 → Morphism (trivial-graph X) (trivial-graph Y)
trivial-morphism f = mk-morphism record
  { apply = id ; map = f }
