{-# OPTIONS --without-K #-}

open import hott.univalence.core

module hott (univalence : ∀ {i} → Univalence i) where

open import hott.level public
open import hott.equivalence public
open import hott.loop public
open import hott.univalence univalence public
open import hott.truncation public
