{-# OPTIONS --without-K #-}
module function.extensionality where

open import function.extensionality.core public
open import function.extensionality.nondep public
  using (ext; ext-id)
open import function.extensionality.dependent public
  using (ext'; ext-id')
open import function.extensionality.strong public
  using (strong-ext; strong-ext-iso)

open import equality.core
open import function.isomorphism
open import function.overloading

-- extensionality for functions of implicit arguments
impl-ext' : ∀ {i j}{X : Set i}{Y : X → Set j}
          → {f g : {x : X} → Y x}
          → ((x : X) → f {x} ≡ g {x})
          → (λ {x} → f {x}) ≡ g
impl-ext' h = cong (apply impl-iso) (ext' h)
