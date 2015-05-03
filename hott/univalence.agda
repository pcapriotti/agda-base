{-# OPTIONS --without-K #-}
open import hott.univalence.core public

module hott.univalence (univalence : ∀ {i} → Univalence i) where

open import hott.univalence.properties univalence public

