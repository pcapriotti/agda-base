{-# OPTIONS --without-K #-}
module overloading.core where

open import level
open import overloading.bundle

record Coercion {i}{j}(Source : Set i)(Target : Set j) : Set (i ⊔ j) where
  constructor coercion
  field
    coerce : Source → Target
open Coercion public

data Style : Set where default : Style

record Styled {i}(style : Style)(X : Set i) : Set i where
  field value : X

styled : ∀ {i}{X : Set i} → (s : Style) → X → Styled s X
styled s x = record { value = x }

coerce-self : ∀ {i} (X : Set i) → Coercion X X
coerce-self {i} _ = record
  { coerce = λ x → x }

coerce-parent : ∀ {i j k}
                {X : Set i}
                {Y : Set j}
              → ⦃ c : Coercion X Y ⦄
              → {Struct : X → Set k}
              → Coercion (Bundle Struct) Y
coerce-parent ⦃ c ⦄ = record
  { coerce = λ x → coerce c (Bundle.parent x) }

set-is-set : ∀ {i} → Coercion (Set i) (Set i)
set-is-set {i} = coerce-self _

∣_∣ : ∀ {i j}{Source : Set i} ⦃ o : Coercion Source (Set j) ⦄
    → Source → Set j
∣_∣ ⦃ c ⦄ = coerce c
