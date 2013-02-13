{-# OPTIONS --without-K #-}
module category.free where

open import sum
open import level
open import equality.core
open import category.category
open import hott.hlevel

open import category.free.list

free-cat : ∀ {i j}{X : Set i}(W : X → X → Set j)
         → h 3 X → h 2 (Σ (X × X) (uncurry W))
         → Category i (i ⊔ j)
free-cat {X = X} W hX hW = record
  { carrier = record
    { obj = X
    ; hom = List W }
  ; is-cat = record
    { id = λ x → nil
    ; _∘_ = λ ws us → us ++ ws
    ; left-unit = nil-right-unit
    ; right-unit = λ _ → refl
    ; associativity = ++-assoc }
  ; trunc = list-hlevel hX hW }
