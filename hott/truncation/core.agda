{-# OPTIONS --without-K #-}
module hott.truncation.core where

open import equality
open import hott.hlevel.core

data ∥_∥ {i}(A : Set i) : Set i where
  η : A → ∥ A ∥

postulate
  trunc-prop : ∀ {i}{A : Set i}
             → (x y : ∥ A ∥) → x ≡ y

elim : ∀ {i j}{A : Set i}
     → {P : ∥ A ∥ → Set j}
     → ((x : ∥ A ∥) → h 1 (P x))
     → ((x : A) → P (η x))
     → (x : ∥ A ∥) → P x
elim _ f (η x) = f x

elim' : ∀ {i j}{A : Set i}{P : Set j}
      → h 1 P
      → (A → P) → ∥ A ∥ → P
elim' _ f (η x) = f x
