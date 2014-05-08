{-# OPTIONS --without-K #-}
module hott.truncation.core where

open import equality
open import hott.hlevel.core

data ∥_∥ (A : Set) : Set where
  η : A → ∥ A ∥

postulate
  trunc-prop : {A : Set}
             → (x y : ∥ A ∥) → x ≡ y

elim : {A : Set}
     → {P : ∥ A ∥ → Set}
     → ((x : ∥ A ∥) → h 1 (P x))
     → ((x : A) → P (η x))
     → (x : ∥ A ∥) → P x
elim _ f (η x) = f x

elim' : {A : Set}{P : Set}
      → h 1 P
      → (A → P) → ∥ A ∥ → P
elim' _ f (η x) = f x
