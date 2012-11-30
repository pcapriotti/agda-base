{-# OPTIONS --without-K #-}
module equality.core where

open import level using ()

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

