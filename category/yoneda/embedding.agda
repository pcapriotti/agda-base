{-# OPTIONS --without-K #-}

open import category.category.core

module category.yoneda.embedding {i j}(C : Category i j) where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.overloading
open import function.extensionality
open import category.category.opposite
open import category.functor.core
open import category.instances.set
open import category.trans.core
open import category.trans.hlevel
open import category.trans.properties
open import category.yoneda.core

open as-category C

-- Yoneda embedding
y : Functor (op C) (Func C (set j))
y = mk-functor {C = op C}{D = Func C (set j)} record
  { apply = hom-func C
  ; map = hom-map C
  ; map-id = λ X → nat-equality
      ( ext' λ _ → ext right-id)
  ; map-hom = λ f g → nat-equality
      ( ext' λ Y → ext' λ h
      → sym (assoc _ _ _) ) }
