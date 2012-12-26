{-# OPTIONS --without-K #-}
module hott.hlevel.properties where

open import hott.hlevel
open import sets.nat

open import hott.hlevel.properties.sets public

h-≤ : ∀ {i n m}{X : Set i}
    → n ≤ m → h n X → h m X
h-≤ (refl-≤ _) hn = hn
h-≤ (suc-≤ p) hn = h↑ _ (h-≤ p hn)
