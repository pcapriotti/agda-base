{-# OPTIONS --without-K #-}
module equality.groupoid where

open import category.groupoid using (Groupoid)
open import equality.core
open import level using (lzero)

equality-groupoid : ∀ {i} (A : Set i) → Groupoid i i
equality-groupoid A = record
  { cat = record
    { obj = A
    ; hom = _≡_
    ; id = λ x → refl {x = x}
    ; _∘_ = λ p q → trans q p
    ; left-unit = left-unit
    ; right-unit = right-unit
    ; associativity = associativity }
  ; _⁻¹ = sym
  ; left-inverse = left-inverse
  ; right-inverse = right-inverse }
  where
    open import equality.properties

module Exports {i}{A : Set i} where
  open import category.category
  open import category.groupoid

  open Groupoid (equality-groupoid A) public
    hiding (id ; _∘_)
open Exports public
