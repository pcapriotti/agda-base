{-# OPTIONS --without-K #-}

module algebra.monoid.category where

open import level
open import category.category using (Category)
open import category.functor.properties
open import algebra.monoid.core
open import algebra.monoid.morphism
open import algebra.monoid.hlevel

-- the category of monoids

mon : ∀ i → Category (lsuc i) i
mon i = record
  { graph = record
    { obj = Monoid i
    ; hom = Morphism }
  ; is-cat = record
    { id = Id
    ; _∘_ = _∘_
    ; left-unit = func-left-unit
    ; right-unit = func-right-unit
    ; associativity = λ f g h → func-assoc h g f }
  ; trunc = morph-hlevel }
