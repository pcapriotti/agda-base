{-# OPTIONS --without-K #-}
module category.instances.discrete where

open import sum
open import category.groupoid
open import category.functor using (Id)
open import equality.core using (_≡_ ; refl ; sym ; trans ; cong)
open import equality.properties
open import function using (id)
open import hott.hlevel

open Groupoid using (cat)

discrete : ∀ {i}→ (A : Set i) → h 3 A → Groupoid i i
discrete A h3 = record
  { cat = record
    { obj = A
    ; hom = _≡_
    ; trunc = h3
    ; id = λ x → refl {x = x}
    ; _∘_ = λ p q → trans q p
    ; left-unit = left-unit
    ; right-unit = right-unit
    ; associativity = associativity }
  ; _⁻¹ = sym
  ; left-inverse = left-inverse
  ; right-inverse = right-inverse }
