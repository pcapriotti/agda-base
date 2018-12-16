module algebra.monoid.mset where

open import level
open import algebra.monoid.core
open import algebra.monoid.morphism
open import algebra.semigroup
open import equality.core

instance
  endoIsSemigroup : ∀ {i} {X : Set i} → IsSemigroup (X → X)
  endoIsSemigroup {X = X} = record
    { _*_ = λ f g x → f (g x)
    ; assoc = λ f g h → refl }

  endoIsMonoid : ∀ {i} {X : Set i} → IsMonoid (X → X)
  endoIsMonoid {X = X} = record
    { sgrp = endoIsSemigroup
    ; e = λ x → x
    ; lunit = λ _ → refl
    ; runit = λ _ → refl }

module _ {i}(M : Set i) ⦃ mM : IsMonoid M ⦄ where
  record IsMSet {j} (X : Set j) : Set (i ⊔ j) where
    field
      _◂_ : M → X → X
      ◂-mor : IsMonoidMorphism _◂_

  open IsMSet ⦃ ... ⦄

  module _ {j k}
           {X : Set j} ⦃ xM : IsMSet X ⦄
           {Y : Set k} ⦃ yM : IsMSet Y ⦄ where
    IsMSetMorphism : (X → Y) → Set (i ⊔ j ⊔ k)
    IsMSetMorphism f = (m : M)(x : X) → f (m ◂ x) ≡ m ◂ f x
