{-# OPTIONS --without-K #-}
module category.instances.set where

open import equality using (refl)
open import function as f
open import level using (lzero ; lsuc)
open import category.category

set : ∀ i → Category (lsuc i) i
set i = record
  { obj = Set i
  ; hom = λ A B → (A → B)
  ; id = λ A → f.id {A = A}
  ; _∘_ = f._∘'_
  ; left-unit = λ f → refl
  ; right-unit = λ f → refl
  ; associativity = λ f g h → refl }