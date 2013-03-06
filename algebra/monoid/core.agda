{-# OPTIONS --without-K #-}

module algebra.monoid.core where

open import level
open import category.graph.core
  hiding (graph; _∘_)
open import category.category
  using (IsCategory; module IsCategory; Category)
open import sets.unit
open import hott.hlevel.core

private
  monoid-graph : ∀ {i} → Set i → Graph lzero i
  monoid-graph X = record
    { obj = ⊤
    ; is-gph = record { hom = λ _ _ → X }  }

IsMonoid : ∀ {i} → Set i → Set i
IsMonoid X = IsCategory (monoid-graph X)

record Monoid i : Set (lsuc i) where
  field
    carrier : Set i
    is-mon : IsMonoid carrier
    trunc : h 2 carrier

  open IsCategory is-mon

  unit : carrier
  unit = id tt

  _⋆_ : carrier → carrier → carrier
  x ⋆ y = y ∘ x

  open IsCategory is-mon public
    hiding (id ; _∘_)

open Monoid public
  using (carrier; is-mon; trunc)
open Monoid ⦃ ... ⦄ public
  hiding (carrier; is-mon; trunc)

graph : ∀ {i} → Monoid i → Graph lzero i
graph M = monoid-graph (carrier M)

as-category : ∀ {i} → Monoid i → Category _ i
as-category M = record
  { graph = graph M
  ; is-cat = is-mon M
  ; trunc = λ _ _ → trunc M }
