{-# OPTIONS --without-K  #-}
module algebra.monoid.mset where

open import level
open import algebra.monoid.core
open import algebra.monoid.morphism
open import algebra.semigroup
open import equality.core
open import hott.level

module _ {i}(M : Set i) ⦃ mM : IsMonoid M ⦄ where
  open IsMonoid ⦃ ... ⦄
  record IsMSet {j} (X : Set j) : Set (i ⊔ j) where
    constructor mk-is-mset
    field
      _◂_ : M → X → X
      ◂-hom : (m₁ m₂ : M)(x : X) → (m₁ * m₂) ◂ x ≡ m₁ ◂ (m₂ ◂ x)
      ◂-id : (x : X) → e ◂ x ≡ x
      mset-level : h 2 X

  open IsMSet ⦃ ... ⦄

  module _ {j k}
           {X : Set j} ⦃ xM : IsMSet X ⦄
           {Y : Set k} ⦃ yM : IsMSet Y ⦄ where
    IsMSetMorphism : (X → Y) → Set (i ⊔ j ⊔ k)
    IsMSetMorphism f = (m : M)(x : X) → f (m ◂ x) ≡ m ◂ f x

    is-mset-morphism-level : h 2 Y → (f : X → Y)
      → h 1 (IsMSetMorphism f)
    is-mset-morphism-level hY f = Π-level λ m → Π-level λ x → hY _ _
