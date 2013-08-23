{-# OPTIONS --without-K #-}
module sets.finite.properties where

open import sum
open import function.isomorphism
open import hott.hlevel.core
open import sets.finite
open import sets.empty

bij-sub-infinite : ∀ {i j}{A : Set i}{P : A → Set j}
                 → ((x : A) → h 1 (P x))
                 → A ≅ Σ A P
                 → (Σ A λ x → ¬ P x)
                 → ¬ (IsFinite A)
bij-sub-infinite hP isom (x₀ , np₀) = {!!}
