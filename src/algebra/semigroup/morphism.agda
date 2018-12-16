module algebra.semigroup.morphism where

open import level
open import algebra.semigroup.core
open import equality.core

module _ {i}{j}
         {X : Set i}⦃ sX : IsSemigroup X ⦄
         {Y : Set j}⦃ sY : IsSemigroup Y ⦄ where
  open IsSemigroup ⦃ ... ⦄

  IsSemigroupMorphism : (X → Y) → Set (i ⊔ j)
  IsSemigroupMorphism f = (x₁ x₂ : X) → f (x₁ * x₂) ≡ f x₁ * f x₂
