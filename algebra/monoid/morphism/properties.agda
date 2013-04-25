{-# OPTIONS --without-K #-}

module algebra.monoid.morphism.properties where

open import equality.core
open import function.core
open import function.isomorphism
open import category.functor
open import algebra.monoid.core
open import algebra.monoid.morphism.core
open import algebra.monoid.morphism.ops

morph-left-unit : ∀ {i j} {M : Monoid i}{N : Monoid j}
                → (f : Morphism M N) → id ∘ f ≡ f
morph-left-unit f = invert (iso≡ morphism-functor-iso)
  (func-left-unit (functor f))

morph-right-unit : ∀ {i j} {M : Monoid i}{N : Monoid j}
                → (f : Morphism M N) → f ∘ id ≡ f
morph-right-unit f = invert (iso≡ morphism-functor-iso)
  (func-right-unit (functor f))

morph-assoc : ∀ {i₀ i₁ i₂ i₃}
              {M₀ : Monoid i₀}{M₁ : Monoid i₁}
              {M₂ : Monoid i₂}{M₃ : Monoid i₃}
              (f : Morphism M₂ M₃)
              (g : Morphism M₁ M₂)
              (h : Morphism M₀ M₁)
            → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
morph-assoc f g h = invert (iso≡ morphism-functor-iso)
  (func-assoc (functor f) (functor g) (functor h))
