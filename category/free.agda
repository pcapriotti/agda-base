{-# OPTIONS --without-K #-}
module category.free where

open import sum
open import level
open import equality.core
open import category.graph
open import category.category
open import hott.hlevel

free-cat : ∀ {i j}(W : Graph i j)
         → h 3 (Graph.obj W)
         → h 2 (Graph.total W)
         → Category i (i ⊔ j)
free-cat W hX hW = record
  { graph = record
    { obj = Graph.obj W
    ; hom = Paths W }
  ; is-cat = record
    { id = λ x → nil
    ; _∘_ = λ ws us → us ++ ws
    ; left-unit = nil-right-unit
    ; right-unit = λ _ → refl
    ; associativity = ++-assoc }
  ; trunc = paths-hlevel hX hW }
