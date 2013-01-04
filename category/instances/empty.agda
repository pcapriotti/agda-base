{-# OPTIONS --without-K #-}
module category.instances.empty where

open import sum
open import category.category
open import category.groupoid
open import category.instances.discrete
open import sets.empty
open import sets.unit
open import hott.hlevel

empty-groupoid : Groupoid _ _
empty-groupoid = discrete (⊥ , h! ⊥-prop)

empty : Category _ _
empty = Groupoid.cat empty-groupoid
