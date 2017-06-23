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
    iso-suc : Fin n ≅ Fin (suc n)
    iso-suc = sym≅ fℕ
           ·≅ isoℕ
           ·≅ ⊎-ap-iso refl≅ fℕ
           ·≅ sym≅ fin-struct-iso
