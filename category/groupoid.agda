{-# OPTIONS --without-K #-}
module category.groupoid where

open import level using (Level ; lsuc ; _⊔_)
open import category.category

record Groupoid (i j : Level) : Set (lsuc (i ⊔ j)) where
  field
    cat : Category i j

  open Category cat

  field
    sym : {A B : obj} → hom A B → hom B A

  _⁻¹_ : {A B : obj} → hom A B → hom B A
  _⁻¹_ = sym

  open Category cat public