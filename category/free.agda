{-# OPTIONS --without-K #-}
module category.free where

open import sum
open import level
open import equality.core
open import category.graph
open import category.category
open import hott.hlevel

free-cat : ∀ {i j}(W : Graph i j)
         → h 3 (obj W)
         → h 2 (total W)
         → Category _ _
free-cat W hX hW = mk-category record
  { obj = obj W
  ; hom = Paths W
  ; id = λ _ → nil
  ; _∘_ = λ ws us → us ++ ws
  ; trunc = paths-hlevel hX hW
  ; left-id = nil-right-unit
  ; right-id = λ _ → refl
  ; assoc = λ ws us vs → ++-assoc vs us ws }
