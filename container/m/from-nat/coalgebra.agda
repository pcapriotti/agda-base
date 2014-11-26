{-# OPTIONS --without-K #-}
module container.m.from-nat.coalgebra where

open import level
open import function.isomorphism
open import sets.nat.core
open import sets.unit
open import container.core
open import container.m.from-nat.core

module _ {li la lb} (c : Container li la lb) where
  open Container c

  X : I → ℕ → Set (la ⊔ lb)
  X i zero = ↑ _ ⊤
  X i (suc n) = F (λ i → X i n) i

  π : (i : I)(n : ℕ) → X i (suc n) → X i n
  π i zero = λ _ → lift tt
  π i (suc n) = imap (λ i → π i n) i

  module _ (i : I) where
    open Limit (X i) (π i) public
    open Limit-shift (X i) (π i) public
  open F-Limit c X π public

  outL-iso : ∀ i → L i ≅ F L i
  outL-iso i = shift-iso i ·≅ lim-iso i
