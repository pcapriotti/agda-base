{-# OPTIONS --without-K #-}

module sets.nat.algebra where

open import equality.core
open import algebra.monoid.core
open import sets.nat.core
open import sets.nat.properties

+-monoid : Monoid _
+-monoid = record
  { carrier = ℕ
  ; is-mon = record
    { id = λ _ → 0
    ; _∘_ = _+_
    ; left-unit = +-left-unit
    ; right-unit = +-right-unit
    ; associativity = λ x y z → +-associativity z y x } }

*-monoid : Monoid _
*-monoid = record
  { carrier = ℕ
  ; is-mon = record
    { id = λ _ → 1
    ; _∘_ = _*_
    ; left-unit = *-left-unit
    ; right-unit = *-right-unit
    ; associativity = λ x y z → *-associativity z y x } }
