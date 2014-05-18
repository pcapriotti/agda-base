{-# OPTIONS --without-K #-}
module hott.truncation.core where

open import equality
open import hott.level.core

private
  module _ {i}(A : Set i) where
    data Trunc : Set i where
      mk-trunc : A → Trunc

∥_∥ : ∀ {i} → Set i → Set i
∥_∥ = Trunc

η : ∀ {i}{A : Set i} → A → ∥ A ∥
η = mk-trunc

postulate
  trunc-prop : ∀ {i}{A : Set i}
             → (x y : ∥ A ∥) → x ≡ y

Trunc-elim' : ∀ {i j}{A : Set i}
            → {P : ∥ A ∥ → Set j}
            → ((x : ∥ A ∥) → h 1 (P x))
            → ((x : A) → P (η x))
            → (x : ∥ A ∥) → P x
Trunc-elim' _ f (mk-trunc x) = f x

Trunc-elim : ∀ {i j}{A : Set i}{P : Set j}
           → h 1 P
           → (A → P) → ∥ A ∥ → P
Trunc-elim _ f (mk-trunc x) = f x
