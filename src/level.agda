{-# OPTIONS --without-K #-}
module level where

open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc)

record ↑ {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open ↑ public
