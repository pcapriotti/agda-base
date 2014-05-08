{-# OPTIONS --without-K #-}
module sets.finite.hlevel where

open import sum
open import function.isomorphism.core
open import hott.hlevel.core
open import hott.hlevel.closure
open import hott.hlevel.sets
open import sets.finite.core

finite-h2 : ∀ {i}{A : Set i} → IsFinite A → h 2 A
finite-h2 (n , fA) = iso-hlevel (sym≅ fA) (fin-set n)
