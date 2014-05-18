{-# OPTIONS --without-K #-}
module sets.finite.level where

open import sum
open import function.isomorphism.core
open import hott.level.core
open import hott.level.closure
open import hott.level.sets
open import sets.finite.core

finite-h2 : ∀ {i}{A : Set i} → IsFinite A → h 2 A
finite-h2 (n , fA) = iso-level (sym≅ fA) (fin-set n)
