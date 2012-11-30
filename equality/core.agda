{-# OPTIONS --without-K #-}
module equality.core where

open import level

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
