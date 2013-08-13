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

  substX : {i : I}{a a' : A i}(p : a ≡ a')(b : B a)
         → X (r (subst B p b)) → X (r b)
  substX refl _ x = x

  substX-β : ∀ {i} {a a' : A i}
             (f : (b : B a) → X (r b))
             (f' : (b : B a') → X (r b))
             (p : a ≡ a')
           → (subst (λ a → (b : B a) → X (r b)) p f ≡ f')
           ≅ ((b : B a) → f b ≡ substX p b (f' (subst B p b)))
  substX-β f f' refl = sym≅ strong-funext-iso

  -- structural equality for container fixpoints
  I-≡ : Set (li ⊔ lx)
  I-≡ = Σ I λ i → X i × X i

  A-≡ : I-≡ → Set la
  A-≡ (_ , u , v) = head u ≡ head v

  B-≡ : {j : I-≡} → A-≡ j → Set lb
  B-≡ {_ , u , _} _ = B (head u)

  r-≡ : {j : I-≡}{p : A-≡ j} → B-≡ p → I-≡
  r-≡ {i , u , v}{p} b = r b , tail u b , substX p b (tail v (subst B p b))

  equality : Container _ _ _
  equality = record
    { I = I-≡
    ; A = A-≡
    ; B = B-≡
    ; r = (λ {j p} → r-≡ {j} {p}) }
