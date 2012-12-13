{-# OPTIONS --without-K #-}
module equality.solver.core where

open import level using (_⊔_)
open import equality.core

Graph : ∀ {i} (X : Set i) → ∀ k → Set _
Graph X k = X → X → Set k

Env : ∀ {i k} {X : Set i} → Graph X k → Set _
Env W = ∀ {x y} → W x y → x ≡ y

record Involution {i k}{X : Set i}(W : Graph X k) : Set (i ⊔ k) where
  field
    τ : ∀ {x y} → W x y → W y x
    τ-τ : ∀ {x y}(w : W x y) → τ (τ w) ≡ w