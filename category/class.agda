{-# OPTIONS --without-K #-}

module category.class where

open import level
open import sum
open import equality.core
open import hott.hlevel

record CatCarrier i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    hom : obj → obj → Set j

record IsCategory {i j}(carrier : CatCarrier i j) : Set (i ⊔ j) where
  infixl 8 _∘_
  open CatCarrier carrier
  field
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
