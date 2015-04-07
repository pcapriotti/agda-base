{-# OPTIONS --without-K #-}
module hott.loop.level where

open import sets.nat.core
open import hott.loop.core
open import hott.level.core

Ω-level : ∀ {i n}{X : Set i}(m : ℕ){x : X}
        → h (m + n) X → h n (Ω m x)
Ω-level zero hX = hX
Ω-level (suc m) hX = Ω-level m (hX _ _)
