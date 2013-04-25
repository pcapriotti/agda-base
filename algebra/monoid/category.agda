{-# OPTIONS --without-K #-}

module algebra.monoid.category where

open import level
open import equality.core
open import function.core
open import category.category
open import category.functor
open import algebra.monoid.core
open import algebra.monoid.morphism

-- the category of monoids

mon : ∀ i → Category _ _
mon i = mk-category record
  { obj = Monoid i
  ; hom = Morphism
  ; id = λ _ → id
  ; _∘_ = _∘_
  ; trunc = morph-hlevel
  ; assoc = morph-assoc
  ; left-id = morph-left-unit
  ; right-id = morph-right-unit }
