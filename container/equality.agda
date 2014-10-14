{-# OPTIONS --without-K #-}

module container.equality where

open import level
open import sum
open import equality.core
open import function.isomorphism
open import function.extensionality
open import container.core
open import container.fixpoint

module Equality {li la lb lx}
                (c : Container li la lb)
                (fp : Fixpoint c lx) where
  open Container c
  open Fixpoint fp

  -- structural equality for container fixpoints
  I-≡ : Set (li ⊔ lx)
  I-≡ = Σ I λ i → X i × X i

  A-≡ : I-≡ → Set la
  A-≡ (_ , u , v) = head u ≡ head v

  B-≡ : {j : I-≡} → A-≡ j → I-≡ → Set _
  B-≡ {i , u , v} p (j , u' , v') =
    Σ (B (head u) j) λ b
    → (tail u j b ≡ u')
    × (tail v j (subst (λ a → B a j) p b) ≡ v')

  equality : Container _ _ _
  equality = record
    { I = I-≡
    ; A = A-≡
    ; B = B-≡ }
