{-# OPTIONS --without-K #-}
module sets.nat.ordering.lt.hlevel where

open import sum
open import equality.core
open import hott.hlevel.core
open import hott.hlevel.closure
open import sets.nat.core
open import sets.nat.ordering.lt.core
open import sets.nat.ordering.leq.hlevel
open import sets.empty
open import container.core
open import container.w

<-hlevel : ∀ {m n} → h 1 (m < n)
<-hlevel = ≤-hlevel
