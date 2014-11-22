{-# OPTIONS --without-K #-}
module hott.level.closure.lift where

open import level
open import function.isomorphism.lift
open import hott.level.core
open import hott.level.closure.core

-- lifting preserves h-levels
↑-level : ∀ {i n} j {X : Set i}
        → h n X
        → h n (↑ j X)
↑-level j {X} = iso-level (lift-iso j X)
