{-# OPTIONS --type-in-type --without-K #-}
module category.instances.unit where

open import level
open import sum
open import category.category
open import category.functor
open import category.groupoid
open import category.instances.discrete
open import sets.unit
open import sets.nat.core
open import hott.hlevel
open import hott.hlevel.properties

unit-groupoid : Groupoid
unit-groupoid = discrete (⊤ , h! ⊤-contr)

unit : Category
unit = cat unit-groupoid

unit-func : (C : Category) → Functor C unit
unit-func C = Const C tt
