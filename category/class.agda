{-# OPTIONS --without-K #-}

module category.class where

open import level
open import sum
open import equality.core
open import hott.hlevel

record IsCategory {i}(obj : Set i) j : Set (i ⊔ lsuc j) where
  infixl 8 _∘_
  field
    hom : obj → obj → Set j

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
