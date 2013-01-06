{-# OPTIONS --without-K #-}

open import category.category hiding (_∘_)
open import category.functor.core using (Functor)
open import category.trans.core
open import category.trans.hlevel
open import category.trans.properties

module category.functor.category {i}{j}{i'}{j'}
  (C : Category i j)(D : Category i' j') where

Func : Category _ _
Func = record
  { carrier = record
    { obj = Functor C D
    ; hom = Nat }
  ; is-cat = record
    { _∘_ = _∘_
    ; id = Id
    ; associativity = nat-assoc
    ; left-unit = nat-left-unit
    ; right-unit = nat-right-unit }
  ; trunc = nat-hset }
