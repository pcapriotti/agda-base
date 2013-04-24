{-# OPTIONS --without-K #-}
module category2.instances.unit where

open import level
open import sum
open import category2.category
open import category2.functor
open import category2.groupoid
open import category2.instances.discrete
open import sets.unit
open import sets.nat.core
open import hott.hlevel
open import hott.hlevel.properties

unit-groupoid : Groupoid _ _
unit-groupoid = discrete (⊤ , h! ⊤-contr)

unit : Category _ _
unit = cat unit-groupoid

unit-func : ∀ {i j}(C : Category i j) → Functor C unit
unit-func C = Const C tt
