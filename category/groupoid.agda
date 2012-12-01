{-# OPTIONS --without-K #-}
module category.groupoid where

open import level using (Level ; lsuc ; _⊔_)
open import category.category
open import equality.core using (_≡_)

record Groupoid (i j : Level) : Set (lsuc (i ⊔ j)) where
  field
    cat : Category i j

  open Category cat

  field
    -- structure
    sym : {A B : obj} → hom A B → hom B A

    -- laws
    left-inverse : {A B : obj}(f : hom A B)
                 → sym f ∘ f ≡ id A

    right-inverse : {A B : obj}(f : hom A B)
                  → f ∘ sym f ≡ id B

  _⁻¹_ : {A B : obj} → hom A B → hom B A
  _⁻¹_ = sym

  open Category cat public