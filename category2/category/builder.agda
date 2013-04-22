{-# OPTIONS --without-K #-}

module category2.category.builder where

open import level
open import equality.core

open import hott.hlevel.core

record Category₀Builder i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    hom : obj → obj → Set j
    id : (x : obj) → hom x x
    _∘_ : {x y z : obj} → hom y z → hom x y → hom x z

record CategoryBuilder i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    hom : obj → obj → Set j
    id : (x : obj) → hom x x
    _∘_ : {x y z : obj} → hom y z → hom x y → hom x z

    left-id : {x y : obj} (f : hom x y) → id y ∘ f ≡ f
    right-id : {x y : obj} (f : hom x y) → f ∘ id x ≡ f
    assoc : {x y z w : obj} (f : hom z w)(g : hom y z)(h : hom x y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

    trunc : (x y : obj) → h 2 (hom x y)
