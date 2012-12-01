{-# OPTIONS --without-K #-}
module equality.core where

open import level using ()

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

sym : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {i} {A : Set i} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl p = p
