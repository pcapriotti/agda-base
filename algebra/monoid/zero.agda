{-# OPTIONS --without-K #-}

module algebra.monoid.zero where

open import level
open import category.graph.trivial
open import category.category.zero
open import overloading.core
open import overloading.bundle
open import sets.unit

IsMonoid₀ : ∀ i (X : Set i) → Set _
IsMonoid₀ _ X = IsCategory₀ _ _ (trivial-graph X)

Monoid₀ : ∀ i → Set _
Monoid₀ i = Bundle (IsMonoid₀ i)

mon₀-is-set : ∀ {i} → Coercion (Monoid₀ i) (Set i)
mon₀-is-set {i} = coerce-parent

mon₀-is-mon₀ : ∀ {i} → Coercion (Monoid₀ i) (Monoid₀ i)
mon₀-is-mon₀ {i} = coerce-self _

mon₀-is-cat₀ : ∀ {i} → Coercion (Monoid₀ i) (Category₀ lzero i)
mon₀-is-cat₀ {i} = record
  { coerce = λ M → bundle (trivial-graph ∣ M ∣)
                           (Bundle.struct M) }

private
  module monoid₀-statics {i j}{Source : Set j}
                         ⦃ c : Coercion Source (Monoid₀ i) ⦄ where
    open Coercion c public using ()
      renaming (coerce to monoid₀)
  module monoid₀-methods {i}{X : Set i}
                         ⦃ s : Styled default (IsMonoid₀ i X) ⦄ where
    open Styled s
    open IsCategory₀ value

    unit : X
    unit = id tt

    _*_ : X → X → X
    x * y = x ∘ y

module as-monoid₀ {i j}{Source : Set j}
                  ⦃ c : Coercion Source (Monoid₀ i) ⦄
                  (source : Source) where
  private target = coerce c source
  _mon₀-instance = styled default (Bundle.struct target)

open monoid₀-statics public
open monoid₀-methods public
