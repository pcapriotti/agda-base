{-# OPTIONS --without-K #-}

module category2.groupoid.internal where

open import level
open import equality.core
open import category2.graph
open import category2.category

record IsGroupoid {i j} (C : Category i j) : Set (lsuc (i ⊔ j)) where
  infix 8 _⁻¹

  open cat-interface C

  field
    _⁻¹ : {x y : obj C} → hom C x y → hom C y x

    left-inverse : {x y : obj C}(f : hom C x y)
                 → (f ⁻¹) ∘ f ≡ id

    right-inverse : {x y : obj C}(f : hom C x y)
                  → f ∘ (f ⁻¹) ≡ id
