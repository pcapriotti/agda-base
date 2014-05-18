{-# OPTIONS --without-K #-}
module higher.circle.core where

open import equality

data S¹ : Set where
  base : S¹

postulate loop : base ≡ base

private
  module Eliminators' {i}(B : S¹ → Set i)
                      (m : B base)
                      (l : subst B loop m ≡ m) where
    elim' : (x : S¹) → B x
    elim' base = m

    β-base' : elim' base ≡ m
    β-base' = refl

    postulate β-loop' : ap' elim' loop ≡ l

private
  module Eliminators {i} {B : Set i}
                     (m : B) (l : m ≡ m) where
    open Eliminators' (λ _ → B) m (subst-const loop m · l)

    elim : S¹ → B
    elim = elim'

    β-base : elim base ≡ m
    β-base = refl

    postulate β-loop : ap elim loop ≡ l

open Eliminators public
open Eliminators' public
