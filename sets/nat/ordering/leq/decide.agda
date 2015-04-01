{-# OPTIONS --without-K #-}
module sets.nat.ordering.leq.decide where

open import decidable
open import sets.core
open import sets.nat.core
open import sets.nat.ordering.leq.core
open import sets.nat.ordering.lt.core

_≤?_ : (n m : ℕ) → Dec (n ≤ m)
0 ≤? m = yes z≤n
suc n ≤? 0 = no λ ()
suc n ≤? suc m with n ≤? m
suc n ≤? suc m | yes p = yes (s≤s p)
suc n ≤? suc m | no u = no λ p → u (ap-pred-≤ p)
