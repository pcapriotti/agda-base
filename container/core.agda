{-# OPTIONS --without-K #-}

module container.core where

open import sum
open import function.core

record Container : Set₁ where
  constructor container
  field
    I : Set
    A : I → Set
    B : {i : I} → A i → Set
    r : {i : I}{a : A i} → B a → I

  -- functor associated to this indexed container
  F : (I → Set) → I → Set
  F X i = Σ (A i) λ a → (b : B a) → X (r b)

  -- homsets in the slice category
  _↝_ : (I → Set) → (I → Set) → Set
  X ↝ Y = {i : I} → X i → Y i

  -- morphism map for the functor F
  imap : (X : I → Set)
       → {Y : I → Set}
       → (X ↝ Y)
       → (F X ↝ F Y)
  imap _ g {i} (a , f) = a , g ∘' f
