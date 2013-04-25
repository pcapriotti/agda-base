{-# OPTIONS --without-K #-}

module algebra.monoid.morphism.builder where

open import level
open import equality.core
open import algebra.monoid.core
open import algebra.monoid.zero
open import overloading.core

record MorphismBuilder {i j}(M : Monoid i)(N : Monoid j) : Set (i ⊔ j) where
  open as-monoid₀ M
  open as-monoid₀ N
  field
    apply : ∣ M ∣ → ∣ N ∣
    map-id : apply unit ≡ unit
    map-hom : (x y : ∣ M ∣) → apply (x * y) ≡ apply x * apply y
