{-# OPTIONS --without-K #-}
module category.instances.discrete {i}(A : Set i) where

open import category.groupoid
open import equality.core using (_≡_ ; refl ; sym ; trans)
open import equality.properties

discrete : Groupoid i i
discrete = record
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
