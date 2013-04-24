{-# OPTIONS --without-K #-}
module category2.terminal where

open import sum
open import equality.core
open import category2.graph
open import category2.category
open import category2.functor using (Const)
open import category2.functor.adjoint
open import category2.instances.unit
open import function.isomorphism
open import sets.unit
open import hott.hlevel
open import hott.hlevel.properties

-- X is a terminal object if the functor X : unit → C
-- is a right adjoint of the unique functor C → unit
terminal : ∀ {i j} (C : Category i j) → obj C → Set _
terminal C X = unit-func C ⊣ Const unit X

private
  module properties {i j}{C : Category i j}
                    (X : obj C)(t : terminal C X) where
    open _⊣_ {D = unit} _ _ t
    open as-category C

    term-univ : (Y : obj C) → contr (hom Y X)
    term-univ Y = iso-hlevel (adj Y tt) (h↑ ⊤-contr tt tt)

    ! : (Y : obj C) → hom Y X
    ! Y = proj₁ (term-univ Y)

open properties public