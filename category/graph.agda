{-# OPTIONS --without-K #-}

module category.graph where

open import level

record Graph i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    hom : obj → obj → Set j
