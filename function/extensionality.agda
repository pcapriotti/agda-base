{-# OPTIONS --without-K #-}
module function.extensionality where

open import function.extensionality.core public
open import function.extensionality.proof public
open import function.extensionality.strong public
  using (strong-funext; strong-funext-iso)

open import equality.core
open import function.isomorphism
open import function.overloading

-- extensionality for functions of implicit arguments
impl-funext : ∀ {i j}{X : Set i}{Y : X → Set j}
          → {f g : {x : X} → Y x}
          → ((x : X) → f {x} ≡ g {x})
          → (λ {x} → f {x}) ≡ g
impl-funext h = cong (apply impl-iso) (funext h)
