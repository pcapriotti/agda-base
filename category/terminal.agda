{-# OPTIONS --without-K #-}
module category.terminal where

open import sum
open import equality.core
open import category.category
open import category.functor using (Const)
open import category.functor.adjoint
open import category.instances.unit
open import function.isomorphism
open import sets.unit
open import hott.hlevel
open import hott.hlevel.properties

-- X is a terminal object if the functor X : unit → C
-- is a right adjoint of the unique functor C → unit
terminal : ∀ {i j} (C : Category i j) → obj C → Set _
terminal C X = unit-func C ⊣ Const unit X

private
  module Properties {i j}{C : Category i j}
                    (X : obj C)(t : terminal C X) where
    open _⊣_ _ _ t
    open Category C using (is-cat)

    term-univ : (Y : obj C) → contr (hom Y X)
    term-univ Y = iso-hlevel (adj Y tt) (h↑ ⊤-contr tt tt) 

    ! : (Y : obj C) → hom Y X
    ! Y = proj₁ (term-univ Y)
    
open Properties public
