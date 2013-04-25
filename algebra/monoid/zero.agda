{-# OPTIONS --without-K #-}

module algebra.monoid.zero where

open import level
open import category.graph.trivial
open import category.category.zero
open import overloading.core
open import sets.unit

IsMonoid₀ : ∀ i (X : Set i) → Set _
IsMonoid₀ _ X = IsCategory₀ _ _ (trivial-graph X)

Monoid₀ : ∀ i → Set _
Monoid₀ i = Bundle (IsMonoid₀ i)

mon₀-is-set : ∀ {i} → Overload _ (Set i)
mon₀-is-set {i} = overload-parent (IsMonoid₀ i)

mon₀-is-mon₀ : ∀ {i} → Overload _ (Monoid₀ i)
mon₀-is-mon₀ {i} = overload-self (Monoid₀ i)

mon₀-is-cat₀ : ∀ {i} → Overload _ (Category₀ lzero i)
mon₀-is-cat₀ {i} = record
  { Source = Monoid₀ i
  ; coerce = λ M → bundle (trivial-graph ∣ M ∣)
                           (Bundle.struct M) }

private
  module monoid₀-statics {i j} ⦃ o : Overload j (Monoid₀ i) ⦄ where
    open Overload o public using ()
      renaming (coerce to monoid₀)
  module monoid₀-methods {i j} ⦃ o : OverloadInstance j default (Monoid₀ i) ⦄ where
    open OverloadInstance o
    open IsCategory₀ (Bundle.struct target)
    private X = ∣ target ∣

    unit : X
    unit = id tt

    _*_ : X → X → X
    x * y = x ∘ y

module as-monoid₀ {i j} ⦃ o : Overload j (Monoid₀ i) ⦄
                  (source : Source o) where
  open overload default (Monoid₀ i) source public

open monoid₀-statics public
open monoid₀-methods public
