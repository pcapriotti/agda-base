{-# OPTIONS --without-K #-}
module category.instances.unit where

open import level
open import sum
open import category.category
open import category.functor
  using (Functor; Const)
open import category.groupoid
open import category.instances.discrete
open import sets.unit
open import sets.nat
open import hott.hlevel
open import hott.hlevel.properties

unit-groupoid : Groupoid _ _
unit-groupoid = discrete (⊤ , h! ⊤-contr)

unit : Category _ _
unit = Groupoid.cat unit-groupoid

unit-func : ∀ {i j}(C : Category i j) → Functor C unit
unit-func C = Const C tt
