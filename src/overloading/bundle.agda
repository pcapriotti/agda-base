{-# OPTIONS --without-K #-}
module overloading.bundle where

open import level

record Bundle {i j} {Base : Set i}
                    (Struct : Base → Set j) : Set (lsuc (i ⊔ j)) where
  constructor bundle
  field
    parent : Base
    struct : Struct parent
