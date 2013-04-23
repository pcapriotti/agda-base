{-# OPTIONS --without-K #-}

module overloading.function where

open import level
open import overloading.core

record Exponential {i j} k (U : Set i) (V : Set j)
                 : Set (i ⊔ j ⊔ lsuc k) where
  constructor exponential
  field
    _⇒_ : U → V → Set k

func-exp : ∀ {i j} → Exponential _ (Set i) (Set j)
func-exp = exponential λ X Y → X → Y

record ExpOverload {i j k} e (U : Set i)(V : Set j)
                   ⦃ exp : Exponential k U V ⦄
                 : Set (i ⊔ j ⊔ k ⊔ lsuc e) where
  open Exponential exp
  field
    X : U
    Y : V
    o : Overload e (X ⇒ Y)

module functions {i j i' j'}
                 ⦃ o₁ : Overload i' (Set i) ⦄
                 ⦃ o₂ : Overload j' (Set j) ⦄
                 (X' : Source o₁)
                 (Y' : Source o₂) where
  X = coerce o₁ X'
  Y = coerce o₂ Y'

  _instance : ExpOverload _ (Set i) (Set j)
  _instance = record
    { X = X
    ; Y = Y
    ; o = overload-self (X → Y) }

private
  module func-methods {i j k} ⦃ eo : ExpOverload k (Set i) (Set j) ⦄ where
    open ExpOverload eo
    open Overload o public using ()
      renaming (coerce to apply)

open func-methods public
