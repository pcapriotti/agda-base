{-# OPTIONS --without-K #-}

module category2.category.opposite where

open import function.core
open import equality.core
open import category2.graph.core
open import category2.category.core

op : ∀ {i j} → Category i j → Category i j
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
