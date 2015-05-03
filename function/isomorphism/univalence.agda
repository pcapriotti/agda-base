{-# OPTIONS --without-K #-}
open import hott.univalence.core

module function.isomorphism.univalence (univalence : ∀ {i} → Univalence i) where

open import equality.core
open import function.core
open import function.isomorphism.core
open import function.extensionality.proof univalence
open import hott.equivalence.alternative funext
open import hott.univalence univalence

≅⇒≡ : ∀ {i}{X Y : Set i}
     → X ≅ Y → X ≡ Y
≅⇒≡ = ≈⇒≡ ∘ ≅⇒≈
