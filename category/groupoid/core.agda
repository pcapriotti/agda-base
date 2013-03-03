{-# OPTIONS --without-K #-}

module category.groupoid.core where

open import level
open import category.category
open import equality.core using (_≡_)

record IsGroupoid {i j} (C : Category i j) : Set (i ⊔ j) where
  constructor groupoid
  infix 9 _⁻¹
  field
    -- structure
    _⁻¹ : {A B : obj C} → hom A B → hom B A

    -- laws
    left-inverse : {A B : obj C}(f : hom A B)
                 → f ⁻¹ ∘ f ≡ id A

    right-inverse : {A B : obj C}(f : hom A B)
                  → f ∘ f ⁻¹ ≡ id B

record Groupoid i j : Set (lsuc (i ⊔ j)) where
  field
    cat : Category i j
    is-grpd : IsGroupoid cat

  open Category cat public
  open IsGroupoid is-grpd public
