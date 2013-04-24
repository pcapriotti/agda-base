{-# OPTIONS --without-K #-}
module category2.instances.empty where

open import sum
open import category2.category
open import category2.functor
open import category2.groupoid
open import category2.instances.discrete
open import sets.empty
open import sets.unit
open import hott.hlevel

empty-groupoid : Groupoid _ _
empty-groupoid = discrete (⊥ , h! ⊥-prop)

empty : Category _ _
empty = cat empty-groupoid

empty-func : ∀ {i j}(C : Category i j) → Functor empty C
empty-func C = mk-functor record
  { apply = ⊥-elim
  ; map = λ {x} _ → ⊥-elim x
  ; map-id = λ x → ⊥-elim x
  ; map-hom = λ {x} _ _ → ⊥-elim x }
