{-# OPTIONS --type-in-type --without-K #-}
module category.instances.empty where

open import sum
open import category.category
open import category.functor
open import category.groupoid
open import category.instances.discrete
open import sets.empty
open import sets.unit
open import hott.hlevel

empty-groupoid : Groupoid
empty-groupoid = discrete (⊥ , h! ⊥-prop)

empty : Category
empty = cat empty-groupoid

empty-func : (C : Category) → Functor empty C
empty-func C = mk-functor record
  { apply = ⊥-elim
  ; map = λ {x} _ → ⊥-elim x
  ; map-id = λ x → ⊥-elim x
  ; map-hom = λ {x} _ _ → ⊥-elim x }
