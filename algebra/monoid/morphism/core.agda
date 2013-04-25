{-# OPTIONS --without-K #-}

module algebra.monoid.morphism.core where

open import level
open import equality.core
open import function.core
open import function.isomorphism
open import function.overloading
open import category.graph.morphism
  hiding (Morphism; mk-morphism)
open import category.graph.trivial
open import category.category
open import category.functor
open import algebra.monoid.core
open import algebra.monoid.morphism.builder
open import sets.unit
open import overloading

record Morphism {i j}(M : Monoid i)(N : Monoid j)
  : Set (lsuc (lsuc (i ⊔ j))) where
  constructor mk-morphism-from-functor
  field as-functor : Functor (cat M) (cat N)

private
  module properties {i j}
                    {M : Monoid i}
                    {N : Monoid j} where
    open Morphism

    mmor-is-fun : Overload _ (∣ M ∣ → ∣ N ∣)
    mmor-is-fun = record
      { Source = Morphism M N
      ; coerce = λ F → map (as-functor F) }

    mmor-is-fct : Overload _ (Functor (cat M) (cat N))
    mmor-is-fct = record
      { Source = Morphism M N
      ; coerce = as-functor }

    mmor-is-mmor : Overload _ (Morphism M N)
    mmor-is-mmor = overload-self (Morphism M N)

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
