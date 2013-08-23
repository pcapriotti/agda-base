{-# OPTIONS --without-K  #-}
module equality.inspect where

open import level
open import equality.core

data _of_is_ {i j}{A : Set i}{B : A → Set j}
            (f : (x : A) → B x)(x : A)(y : B x) : Set (i ⊔ j) where
  [_] : f x ≡ y → f of x is y

inspect : ∀ {i j}{A : Set i}{B : A → Set j}
        → (f : (x : A)→ B x)(x : A)
        → f of x is f x
inspect f x = [ refl ]
