{-# OPTIONS --without-K #-}
module sets.core where

open import equality.core

module _ {A : Set}
         (_<_ : A → A → Set) where
  data Ordering (x y : A) : Set where
    lt : x < y → Ordering x y
    eq : x ≡ y → Ordering x y
    gt : y < x → Ordering x y
