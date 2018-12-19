module algebra.semigroup.morphism where

open import level
open import algebra.semigroup.core
open import equality.core
open import hott.level

module _ {i}{j}
         {X : Set i}⦃ sX : IsSemigroup X ⦄
         {Y : Set j}⦃ sY : IsSemigroup Y ⦄ where
  open IsSemigroup ⦃ ... ⦄

  IsSemigroupMorphism : (X → Y) → Set (i ⊔ j)
  IsSemigroupMorphism f = (x₁ x₂ : X) → f (x₁ * x₂) ≡ f x₁ * f x₂

  is-semigroup-morphism-level : (f : X → Y) → h 1 (IsSemigroupMorphism f)
  is-semigroup-morphism-level f = Π-level λ x₁ → Π-level λ x₂ → is-set _ _
