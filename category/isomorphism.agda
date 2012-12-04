{-# OPTIONS --without-K #-}
open import category.category

module category.isomorphism {i j}(C : Category i j) where

open import equality.core using (_≡_ ; refl)

open Category C

record _≅_ (x y : obj) : Set j where
  constructor iso
  field
    to : hom x y
    from : hom y x

    iso₁ : from ∘ to ≡ id x
    iso₂ : to ∘ from ≡ id y