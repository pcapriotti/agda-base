{-# OPTIONS --type-in-type --without-K #-}

open import category.category.core

module category.yoneda.core (C : Category) where

open import sum
open import function.core
open import function.extensionality
open import category.graph.core
open import category.functor.core
open import category.instances.set
open import category.trans.core

open as-category C

hom-func : obj C → Functor C set
hom-func X = mk-functor {D = set} record
  { apply = λ Y → (hom X Y , trunc X Y)
  ; map = _∘_
  ; map-id = λ _ → ext left-id
  ; map-hom = λ f g → ext λ _ → assoc _ _ _ }

hom-map : {X X' : obj C}(f : hom X X') → hom-func X' ⇒ hom-func X
hom-map f = record
  { α = λ Y g → g ∘ f
  ; α-nat = λ h → ext λ g → assoc h g f }
