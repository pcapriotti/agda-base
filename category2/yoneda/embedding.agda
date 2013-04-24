{-# OPTIONS --without-K #-}

open import category2.category.core

module category2.yoneda.embedding {i j}(C : Category i j) where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.overloading
open import function.extensionality
open import category2.category.opposite
open import category2.functor.core
open import category2.instances.set
open import category2.trans.core
open import category2.trans.hlevel
open import category2.trans.properties
open import category2.yoneda.core

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
