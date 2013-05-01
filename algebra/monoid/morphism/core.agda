{-# OPTIONS --without-K #-}

module algebra.monoid.morphism.core where

open import level
open import equality.core
open import function.core
open import function.isomorphism
open import function.overloading
import category.graph.morphism as G
open import category.graph.trivial
open import category.category
open import category.functor
open import algebra.monoid.core
open import algebra.monoid.morphism.builder
open import sets.unit
open import overloading
open import hott.univalence

record Morphism {i j}(M : Monoid i)(N : Monoid j)
  : Set (lsuc (lsuc (i ⊔ j))) where
  constructor mk-morphism-from-functor
  field as-functor : Functor (cat M) (cat N)

morphism-functor-iso : ∀ {i j}{M : Monoid i}{N : Monoid j}
                     → Morphism M N
                     ≅ Functor (cat M) (cat N)
morphism-functor-iso = record
  { to = as-functor
  ; from = mk-morphism-from-functor
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }
  where open Morphism

morphism-functor-eq : ∀ {i j}{M : Monoid i}{N : Monoid j}
                    → Morphism M N ≡ Functor (cat M) (cat N)
morphism-functor-eq = ≅⇒≡ morphism-functor-iso

private
  module properties {i j}
                    {M : Monoid i}
                    {N : Monoid j} where
    open Morphism

    mmor-is-fun : Coercion (Morphism M N) (∣ M ∣ → ∣ N ∣)
    mmor-is-fun = record
      { coerce = λ F → G.map (as-functor F) }

    mmor-is-fct : Coercion (Morphism M N) (Functor (cat M) (cat N))
    mmor-is-fct = record
      { coerce = as-functor }

    mmor-is-mmor : Coercion (Morphism M N) (Morphism M N)
    mmor-is-mmor = coerce-self _
open properties public

mk-morphism : ∀ {i j}{M : Monoid i}{N : Monoid j}
            → MorphismBuilder M N → Morphism M N
mk-morphism {M = M}{N = N} b = mk-morphism-from-functor F
  where
    module B = MorphismBuilder b
    F : Functor (cat M) (cat N)
    F = mk-functor {C = cat M}{D = cat N} record
      { apply = λ x → x
      ; map = B.apply
      ; map-id = λ _ → B.map-id
      ; map-hom = B.map-hom }
