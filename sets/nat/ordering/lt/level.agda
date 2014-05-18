{-# OPTIONS --without-K #-}
module sets.nat.ordering.lt.level where

open import sum
open import equality.core
open import hott.level.core
open import hott.level.closure
open import sets.nat.core
open import sets.nat.ordering.lt.core
open import sets.nat.ordering.leq.level
open import sets.empty
open import container.core
open import container.w

<-level : ∀ {m n} → h 1 (m < n)
<-level = ≤-level
