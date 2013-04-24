{-# OPTIONS --without-K #-}

module container.fixpoint where

open import sum
open import level
open import container.core
open import function.core
open import function.isomorphism
open import function.overloading

record Fixpoint {li la lb}
                (c : Container li la lb)
                (lx : Level) : Set (li ⊔ la ⊔ lb ⊔ lsuc lx) where
  constructor fix

  open Container c
  field
    X : I → Set lx
    fixpoint : ∀ i → X i ≅ F X i

  head : X ↝ A
  head {i} = proj₁ ∘ apply (fixpoint i)

  tail : ∀ {i}(u : X i)(b : B (head u)) → X (r b)
  tail {i} = proj₂ ∘' apply (fixpoint i)
