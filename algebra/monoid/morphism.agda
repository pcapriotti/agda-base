{-# OPTIONS --without-K #-}

module algebra.monoid.morphism where

open import level
open import equality.core
open import function.core
open import function.isomorphism
open import function.overloading
open import category.category
open import category.functor
open import algebra.monoid.core
open import sets.unit
open import overloading
open import category.graph.morphism
  hiding (IsMorphism; Morphism)
open import category.graph.trivial

IsMorphism : ∀ {i j} (M : Monoid i)(N : Monoid j)
           → (f : ∣ M ∣ → ∣ N ∣) → Set _
IsMorphism M N f = IsFunctor (cat M) (cat N) (trivial-morphism f)

Morphism : ∀ {i j} → Monoid i → Monoid j → Set _
Morphism M N = Bundle (IsMorphism M N)

functor-morphism-iso : ∀ {i j}{M : Monoid i}{N : Monoid j}
                     → Functor (cat M) (cat N)
                     ≅ Morphism M N
functor-morphism-iso = record
  { to = λ F → bundle (map F {tt}{tt}) (Bundle.struct F)
  ; from = λ F → bundle (trivial-morphism (Bundle.parent F))
                         (Bundle.struct F)
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

private
  Id : ∀ {i} → (M : Monoid i) → Morphism M M
  Id M = apply functor-morphism-iso id

  -- module Morphism {i j}{M : Monoid i}{N : Monoid j}
  --                 (f : Morphism M N) where
  --   module Func = F.Functor f
  --   open mon-interface M
  --   open mon-interface N
  -- 
  --   map : carrier M → carrier N
  --   map = Func.map
  -- 
  --   map-id : map unit ≡ unit
  --   map-id = Func.map-id tt
  -- 
  --   map-hom : ∀ x y → map (x ⋆ y) ≡ map x ⋆ map y
  --   map-hom = Func.map-hom
