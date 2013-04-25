{-# OPTIONS --without-K #-}

module algebra.structure where

open import level

record AlgStruct {s i} (Sort : Set s) : Set (lsuc i ⊔ s) where
  field carrier : Sort → Set i

open AlgStruct ⦃ ... ⦄ public
