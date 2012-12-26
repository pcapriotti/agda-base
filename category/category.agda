{-# OPTIONS --without-K #-}

module category.category where

open import level using (Level ; lsuc ; _⊔_)
open import sum
open import equality.core using (_≡_)
open import hott.hlevel

record Category (i j : Level) : Set (lsuc (i ⊔ j)) where
  infixl 8 _∘_
  field
    obj : Set i
    hom : obj → obj → Set j

    trunc : ∀ x y → h 2 (hom x y)

    id : (A : obj) → hom A A
    _∘_ : {A B C : obj} → hom B C → hom A B → hom A C

    left-unit : {A B : obj}(f : hom A B)
              → id B ∘ f ≡ f
    right-unit : {A B : obj}(f : hom A B)
               → f ∘ id A ≡ f
    associativity : {A B C D : obj}
                    (f : hom A B)
                    (g : hom B C)
                    (h : hom C D)
                  → h ∘ g ∘ f ≡ h ∘ (g ∘ f)

  mor : Set (i ⊔ j)
  mor = Σ (obj × obj) (uncurry hom)
