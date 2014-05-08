{-# OPTIONS --without-K #-}
module sets.nat.ordering.leq.decide where

open import decidable
open import sets.core
open import sets.nat.core
open import sets.nat.ordering.leq.core
open import sets.nat.ordering.lt.core

_≤?_ : (n m : ℕ) → Dec (n ≤ m)
n ≤? m with compare n m
... | lt p = yes (<⇒≤ p)
... | eq p = yes (≡⇒≤ p)
... | gt p = no (λ q → suc≰ (trans≤ p q))
