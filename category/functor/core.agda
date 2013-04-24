{-# OPTIONS --without-K #-}

module category.functor.core {i j i' j'} where

open import level
open import equality.core
open import function.core
open import overloading
open import category.category.core
open import category.functor.builder
open import category.graph.core
open import category.graph.morphism

record IsFunctor (C : Category i j)
                 (D : Category i' j')
                 (F : Morphism (graph C) (graph D)) : Set (i ⊔ j ⊔ j') where
  open as-category C
  open as-category D

  field
    map-id : (x : obj C) → map F (id {X = x}) ≡ id
    map-hom : {x y z : obj C} (f : hom y z) (g : hom x y)
            → map F (f ∘ g) ≡ map F f ∘ map F g

Functor : Category i j → Category i' j' → Set _
Functor C D = Bundle (IsFunctor C D)

private
  module properties {C : Category i j}
                    {D : Category i' j'} where

    fct-is-fun : Overload _ (obj C → obj D)
    fct-is-fun = overload-parent (IsFunctor C D)

    fct-is-mor : Overload _ (Morphism (graph C) (graph D))
    fct-is-mor = overload-parent (IsFunctor C D)

    fct-is-fct : Overload _ (Functor C D)
    fct-is-fct = overload-self (Functor C D)

    private
      module functor-methods {k} ⦃ o : Overload k (Functor C D) ⦄ where
        private
          module with-source (source : Source o) where
            private target = coerce o source
            open IsFunctor (Bundle.struct target) public
        open with-source public

    open functor-methods public

    mk-functor : FunctorBuilder C D → Functor C D
    mk-functor b = let module B = FunctorBuilder b in record
      { parent = mk-morphism record
        { apply = B.apply
        ; map = B.map }
      ; struct = record
        { map-id = B.map-id
        ; map-hom = B.map-hom } }
open properties public
