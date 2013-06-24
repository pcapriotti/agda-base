{-# OPTIONS --without-K --type-in-type #-}

module category.category.opposite where

open import function.core
open import equality.core
open import category.graph.core
open import category.category.core

op : Category → Category
op C = mk-category record
  { obj = obj C
  ; hom = λ x y → hom y x
  ; id = λ _ → id
  ; _∘_ = λ f g → g ∘ f
  ; trunc = λ x y → trunc y x
  ; left-id = right-id
  ; right-id = left-id
  ; assoc = λ f g h → sym (assoc h g f) }
  where open as-category C
