{-# OPTIONS --without-K #-}

module higher.interval where

open import Relation.Binary.PropositionalEquality

open import equality-groupoid

postulate
  I : Set

  zero : I
  one : I
  path : zero ≡ one


module DepElim (B : I → Set)
               (x : B zero)
               (y : B one)
               (p : subst B path x ≡ y) where
  postulate
    elim : (t : I) → B t
    β-zero : elim zero ≡ x
    β-one : elim one ≡ y
    β-path : ap (subst B path) (sym β-zero)
           · lem-naturality elim path
           · β-one
           ≡ p

module Elim {X : Set}
            (x y : X)
            (p : x ≡ y) where
  open DepElim (λ _ → X) x y p

  postulate
    elim' : I → X
    β-zero' : elim zero ≡ x
    β-one' : elim one ≡ y
    β-path' : sym (β-zero') · ap elim path · β-one' ≡ p