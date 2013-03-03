{-# OPTIONS --without-K #-}

module algebra.group.core where

open import level
open import category.groupoid
open import algebra.monoid.core

-- a group structure is a groupoid structure on a monoid
IsGroup : ∀ {i} → Monoid i → Set i
IsGroup M = IsGroupoid (as-category M)

module IsGroup {i}{M : Monoid i}(is-grp : IsGroup M)
  = IsGroupoid is-grp

-- a group is a monoid together with a group structure
record Group i : Set (lsuc i) where
  field
    mon : Monoid i
    is-grp : IsGroup mon

  open Monoid mon public
  open IsGroup is-grp public
