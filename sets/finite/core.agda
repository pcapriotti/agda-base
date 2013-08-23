{-# OPTIONS --without-K #-}
module sets.finite.core where

open import function.isomorphism
open import sets.nat
open import sets.fin

record IsFinite {i}(A : Set i) : Set i where
  field
    size : ℕ
    enum : Fin size ≅ A

fin-is-finite : ∀ {n} → IsFinite (Fin n)
fin-is-finite {n} = record
  { size = n
  ; enum = refl≅ }

--ℕ-is-infinite : ¬ (IsFinite ℕ)
--ℕ-is-infinite
