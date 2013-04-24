{-# OPTIONS --without-K #-}
module category2.univalence where

open import sum
open import equality.core
open import function.isomorphism
open import category2.category
open import category2.graph
open import category2.isomorphism
open import hott.weak-equivalence
open import hott.hlevel

univalent : ∀ {i j} → Category i j → Set _
univalent C = (x y : obj C) → weak-equiv (≡⇒iso C {x}{y})

univalent-h1 : ∀ {i j}(C : Category i j) → h 1 (univalent C)
univalent-h1 C = Π-hlevel λ x → Π-hlevel λ y → weak-equiv-h1 _

private
  module properties {i j}{C : Category i j}(univ : univalent C) where
    iso≅eq : (x y : obj C) → (x ≡ y) ≅ cat-iso C x y
    iso≅eq x y = ≈⇒≅ (≡⇒iso C , univ x y)

    -- the object set of a univalent category has h-level 3
    obj-h3 : h 3 (obj C)
    obj-h3 x y = iso-hlevel (sym≅ (iso≅eq x y)) (cat-iso-hset x y)
open properties public
