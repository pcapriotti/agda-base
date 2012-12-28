{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import function.extensionality
open import category.category
open import category.functor
open import category.trans
  using (_⇒_)
open import category.trans.hlevel
  using (nat-equality)
open import category.instances.set

module category.yoneda {i j}(C : Category i j) where

open Category C
  renaming (_∘_ to _⋆_)

hom-func : obj → Functor C (set j)
hom-func X = record
  { apply = λ Y → (hom X Y , trunc X Y)
  ; map = _⋆_
  ; map-id = λ _ → extensionality _ _ λ x → left-unit x
  ; map-hom = λ f g → extensionality _ _ λ x → associativity x f g }

hom-map : {X X' : obj}(f : hom X X') → hom-func X' ⇒ hom-func X
hom-map f = record
  { α = λ Y g → g ⋆ f
  ; α-nat = λ h → extensionality _ _ λ g → associativity f g h }

-- Yoneda embedding
y : Functor (op C) (Func C (set j))
y = record
  { apply = hom-func
  ; map = hom-map
  ; map-id = λ X → nat-equality _ _
      ( extensionality' _ _ λ _
      → extensionality _ _
        right-unit)
  ; map-hom = λ g f → nat-equality _ _
      ( extensionality' _ _ λ _
      → extensionality _ _ λ h
      → sym (associativity f g h) ) }
