{-# OPTIONS --without-K #-}
module sets.core where

open import equality.core

module _ {i}{A : Set i}
         (_<_ : A → A → Set i) where
  data Ordering (x y : A) : Set i where
    lt : x < y → Ordering x y
    eq : x ≡ y → Ordering x y
    gt : y < x → Ordering x y
