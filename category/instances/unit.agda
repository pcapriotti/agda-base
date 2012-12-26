{-# OPTIONS --without-K #-}
module category.instances.unit where

open import level
open import category.category
open import category.groupoid
open import category.instances.discrete
open import sets.unit
open import sets.nat
open import hott.hlevel
open import hott.hlevel.properties

unit-groupoid : Groupoid _ _
unit-groupoid = discrete ⊤ (h-≤ (zero-min 3) ⊤-contr)

unit : Category _ _
unit = Groupoid.cat unit-groupoid
