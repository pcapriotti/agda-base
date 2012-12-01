{-# OPTIONS --without-K #-}

module category.category where

open import level using (Level ; lsuc ; _⊔_)
open import equality.core using (_≡_)

record Category (i j : Level) : Set (lsuc (i ⊔ j)) where
  infixl 9 _∘_
  field
    -- data
    obj : Set i
    hom : obj → obj → Set j

    -- structure
    id : (A : obj) → hom A A
    _∘_ : {A B C : obj} → hom B C → hom A B → hom A C

    -- laws
    left-unit : {A B : obj}(f : hom A B)
              → id B ∘ f ≡ f
    right-unit : {A B : obj}(f : hom A B)
               → f ∘ id A ≡ f
    associativity : {A B C D : obj}
                    (f : hom A B)
                    (g : hom B C)
                    (h : hom C D)
                  → h ∘ g ∘ f ≡ h ∘ (g ∘ f)

  -- reverse composition
  _⊚_ : {A B C : obj} → hom A B → hom B C → hom A C
  g ⊚ f = f ∘ g