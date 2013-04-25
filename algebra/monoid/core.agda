{-# OPTIONS --without-K #-}

module algebra.monoid.core where

open import level
open import algebra.monoid.zero
open import category.graph.trivial
open import category.category.zero
open import category.category.core
open import overloading.core

IsMonoid : ∀ i (M : Monoid₀ i) → Set _
IsMonoid _ M = IsCategory _ _ (cat₀ M)

Monoid : ∀ i → Set _
Monoid i = Bundle (IsMonoid i)

mon-is-set : ∀ {i} → Overload _ (Set i)
mon-is-set {i} = overload-parent (IsMonoid i)

mon-is-mon₀ : ∀ {i} → Overload _ (Monoid₀ i)
mon-is-mon₀ {i} = overload-parent (IsMonoid i)

mon-is-mon : ∀ {i} → Overload _ (Monoid i)
mon-is-mon {i} = overload-self (Monoid i)

mon-is-cat₀ : ∀ {i} → Overload _ (Category₀ lzero i)
mon-is-cat₀ {i} = overload-parent (IsMonoid i)

mon-is-cat : ∀ {i} → Overload _ (Category lzero i)
mon-is-cat {i} = record
  { Source = Monoid i
  ; coerce = λ M → bundle (cat₀ M) (Bundle.struct M) }

private
  module monoid-statics {i j} ⦃ o : Overload j (Monoid i) ⦄ where
    open Overload o public using ()
      renaming (coerce to monoid)
  module monoid-methods {i j} ⦃ o : OverloadInstance j default (Monoid i) ⦄ where
    open OverloadInstance o
    open IsCategory (Bundle.struct target) public
      renaming ( left-id to *-left-id
               ; right-id to *-right-id
               ; assoc to *-assoc
               ; trunc to mtrunc )

module as-monoid {i j} ⦃ o : Overload j (Monoid i) ⦄
                  (source : Source o) where
  private target = coerce o source
  open as-monoid₀ target public
    renaming (_instance to _parent-instance)
  open overload default (Monoid i) target public

open monoid-statics public
open monoid-methods public
