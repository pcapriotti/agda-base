{-# OPTIONS --without-K #-}

module container.core where

open import level
open import sum
open import function.core

record Container (li la lb : Level) : Set (lsuc (li ⊔ la ⊔ lb)) where
  constructor container
  field
    I : Set li
    A : I → Set la
    B : {i : I} → A i → I → Set lb

  -- functor associated to this indexed container
  F : ∀ {lx} → (I → Set lx) → I → Set _
  F X i = Σ (A i) λ a → ∀ j → B a j → X j

  -- homsets in the slice category
  _↝_ : ∀ {lx ly} → (I → Set lx) → (I → Set ly) → Set _
  X ↝ Y = {i : I} → X i → Y i

  -- morphism map for the functor F
  imap : ∀ {lx ly}
       → (X : I → Set lx)
       → {Y : I → Set ly}
       → (X ↝ Y)
       → (F X ↝ F Y)
  imap _ g {i} (a , u) = a , λ j → g ∘' u j
