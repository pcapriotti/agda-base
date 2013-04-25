{-# OPTIONS --without-K #-}

module algebra.monoid.morphism.ops where

open import function.core
open import algebra.monoid.core
open import algebra.monoid.morphism.core
open import category.functor.ops

private
  Id : ∀ {i} (M : Monoid i) → Morphism M M
  Id M = mk-morphism-from-functor id

  Compose : ∀ {i j k}
          → {M : Monoid i}{N : Monoid j}{P : Monoid k}
          → Morphism N P → Morphism M N → Morphism M P
  Compose (mk-morphism-from-functor F)
          (mk-morphism-from-functor G)
         = mk-morphism-from-functor (F ∘ G)

mmor-identity : ∀ {i} → Identity _ _
mmor-identity {i} = record
  { U = Monoid i
  ; endo = λ M → Morphism M M
  ; id = λ {M} → Id M }

mmor-comp : ∀ {i j k} → Composition _ _ _ _ _ _
mmor-comp {i}{j}{k} = record
  { U₁ = Monoid i
  ; U₂ = Monoid j
  ; U₃ = Monoid k
  ; hom₁₂ = Morphism
  ; hom₂₃ = Morphism
  ; hom₁₃ = Morphism
  ; _∘_ = Compose }
