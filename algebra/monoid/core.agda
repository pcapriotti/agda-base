{-# OPTIONS --without-K #-}

module algebra.monoid.core where

open import level
open import algebra.monoid.zero
open import category.graph.trivial
open import category.category.zero
open import category.category.core
open import overloading.core
open import overloading.bundle

IsMonoid : ∀ i (M : Monoid₀ i) → Set _
IsMonoid _ M = IsCategory _ _ (cat₀ M)

Monoid : ∀ i → Set _
Monoid i = Bundle (IsMonoid i)

mon-is-set : ∀ {i} → Coercion (Monoid i) (Set i)
mon-is-set {i} = coerce-parent

mon-is-mon₀ : ∀ {i} → Coercion (Monoid i) (Monoid₀ i)
mon-is-mon₀ {i} = coerce-parent

mon-is-mon : ∀ {i} → Coercion (Monoid i) (Monoid i)
mon-is-mon {i} = coerce-self _

mon-is-cat₀ : ∀ {i} → Coercion (Monoid i) (Category₀ lzero i)
mon-is-cat₀ {i} = coerce-parent

mon-is-cat : ∀ {i} → Coercion (Monoid i) (Category lzero i)
mon-is-cat {i} = record
  { coerce = λ M → bundle (cat₀ M) (Bundle.struct M) }

private
  module monoid-statics {i j}{Source : Set j}
                        ⦃ c : Coercion Source (Monoid i) ⦄ where
    open Coercion c public using ()
      renaming (coerce to monoid)
  module monoid-methods {i}{M : Monoid₀ i}
                        ⦃ s : Styled default (IsMonoid i M) ⦄ where
    open Styled s
    open IsCategory value public
      renaming ( left-id to *-left-id
               ; right-id to *-right-id
               ; assoc to *-assoc
               ; trunc to mtrunc )

module as-monoid {i j}{Source : Set j}
                 ⦃ c : Coercion Source (Monoid i) ⦄
                 (source : Source) where
  private target = coerce c source
  open as-monoid₀ target public
  _mon-instance = styled default (Bundle.struct target)

open monoid-statics public
open monoid-methods public
