{-# OPTIONS --without-K --type-in-type #-}
module overloading.bundle where


record Bundle {Base : Set}
              (Struct : Base → Set) : Set where
  constructor bundle
  field
    parent : Base
    struct : Struct parent
