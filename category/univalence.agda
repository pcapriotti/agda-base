{-# OPTIONS --without-K #-}
module category.univalence where

open import sum
open import equality.core
open import function.isomorphism
open import category.category
open import category.isomorphism
open import hott.weak-equivalence
open import hott.hlevel

open Category

univalent : ∀ {i j} → Category i j → Set _
univalent C = (x y : obj C) → weak-equiv (≡⇒iso C {x}{y})

private
  module Properties {i j}{C : Category i j}(univ : univalent C) where
    iso≅eq : (x y : obj C) → (x ≡ y) ≅ cat-iso C x y
    iso≅eq x y = ≈⇒≅ (≡⇒iso C , univ x y)
  
    -- the object set of a univalent category has h-level 3
    obj-h3 : h 3 (obj C)
    obj-h3 x y = iso-hlevel (sym≅ (iso≅eq x y)) (cat-iso-hset x y)
