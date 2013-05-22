{-# OPTIONS --without-K --type-in-type #-}

module category.functor.core where

open import level
open import equality.core
open import function.core
open import overloading.core
open import overloading.bundle
open import category.category.core
open import category.functor.builder
open import category.graph.core
open import category.graph.morphism.core

private
  module definitions (C : Category)
                     (D : Category)
                     (F : Morphism (graph C) (graph D)) where
    open as-category C
    open as-category D

    MapId : Set
    MapId = (x : obj C) → map F (id {X = x}) ≡ id

    MapHom : Set
    MapHom = {x y z : obj C}
           → (f : hom y z)
           → (g : hom x y)
           → map F (f ∘ g)
           ≡ map F f ∘ map F g
open definitions public

record IsFunctor (C : Category)
                 (D : Category)
                 (F : Morphism (graph C) (graph D)) : Set where
  open as-category C
  open as-category D

  field
    map-id : MapId C D F
    map-hom : MapHom C D F

Functor : Category → Category → Set
Functor C D = Bundle (IsFunctor C D)

private
  module properties {C : Category}
                    {D : Category} where

    fct-is-fun : Coercion (Functor C D) (obj C → obj D)
    fct-is-fun = coerce-parent

    fct-is-mor : Coercion (Functor C D) (Morphism (graph C) (graph D))
    fct-is-mor = coerce-parent

    fct-is-fct : Coercion (Functor C D) (Functor C D)
    fct-is-fct = coerce-self _

    private
      module functor-methods {Source : Set}
                             ⦃ c : Coercion Source (Functor C D) ⦄ where
        open Coercion c public using ()
          renaming (coerce to functor)
      module functor-explicits {Source : Set}
                               ⦃ c : Coercion Source (Functor C D) ⦄
                               (source : Source) where
        private target = coerce c source
        open IsFunctor (Bundle.struct target) public

    open functor-methods public
    open functor-explicits public

    mk-functor : FunctorBuilder C D → Functor C D
    mk-functor b = let module B = FunctorBuilder b in record
      { parent = mk-morphism record
        { apply = B.apply
        ; map = B.map }
      ; struct = record
        { map-id = B.map-id
        ; map-hom = B.map-hom } }
open properties public
