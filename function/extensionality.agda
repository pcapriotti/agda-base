{-# OPTIONS --without-K #-}
open import hott.univalence.core

module function.extensionality (univalence : ∀ {i} → Univalence i) where

open import function.extensionality.core public
open import function.extensionality.proof univalence public
open import function.extensionality.strong funext public
  using (strong-funext; strong-funext-iso)
open import function.extensionality.computation public

open import equality.core
open import function.isomorphism.utils
open import function.overloading

-- extensionality for functions of implicit arguments
impl-funext : ∀ {i j}{X : Set i}{Y : X → Set j}
          → {f g : {x : X} → Y x}
          → ((x : X) → f {x} ≡ g {x})
          → (λ {x} → f {x}) ≡ g
impl-funext h = ap (apply impl-iso) (funext h)
