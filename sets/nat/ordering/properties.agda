{-# OPTIONS --without-K #-}
module sets.nat.ordering.properties where

open import function.isomorphism
open import sets.nat.core
open import sets.nat.ordering.lt
open import sets.nat.ordering.leq
open import hott.level.core

<-≤-iso : ∀ {n m} → (n < m) ≅ (suc n ≤ m)
<-≤-iso = record
  { to = f
  ; from = g
  ; iso₁ = λ _ → h1⇒prop <-level _ _
  ; iso₂ = λ _ → h1⇒prop ≤-level _ _ }
  where
    f : ∀ {n m} → n < m → suc n ≤ m
    f suc< = refl-≤
    f (n<s p) = s≤s (trans-≤ suc≤ (f p))

    g : ∀ {n m} → suc n ≤ m → n < m
    g {zero} (s≤s p) = z<n
    g {suc n} (s≤s p) = ap<-suc (g p)
