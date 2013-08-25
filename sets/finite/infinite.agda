{-# OPTIONS --without-K #-}
module sets.finite.infinite where

open import sum
open import equality.core
open import function.isomorphism.core
open import function.isomorphism.utils
open import sets.nat
open import sets.empty
open import sets.unit
open import sets.fin.core
open import sets.fin.properties
open import sets.fin.universe
open import sets.finite.core

ℕ-not-finite : ¬ (IsFinite ℕ)
ℕ-not-finite (n , fℕ) = suc-fixpoint (sym (Fin-inj iso-suc))
  where
    isoℕ : ℕ ≅ (⊤ ⊎ ℕ)
    isoℕ = record
      { to = λ { zero → inj₁ tt ; (suc n) → inj₂ n }
      ; from = λ { (inj₁ _) → zero ; (inj₂ n) → suc n }
      ; iso₁ = λ { zero → refl ; (suc n) → refl }
      ; iso₂ = λ { (inj₁ _) → refl ; (inj₂ n) → refl } }

    iso-suc : Fin n ≅ Fin (suc n)
    iso-suc = sym≅ fℕ
           ·≅ isoℕ
           ·≅ ⊎-ap-iso refl≅ fℕ
           ·≅ sym≅ fin-struct-iso
