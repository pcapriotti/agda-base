{-# OPTIONS --without-K #-}

module category2.functor.core {i j i' j'} where

open import level
open import equality.core
open import function.core
open import overloading
open import category2.category.core
open import category2.functor.builder
open import category2.graph.core
open import category2.graph.morphism

record IsFunctor {C : Category i j}
                 {D : Category i' j'}
                 (F : Morphism (graph C) (graph D)) : Set (i ⊔ j ⊔ j') where
  open as-category C
  open as-category D

  field
    map-id : (x : obj C) → map F (id {X = x}) ≡ id
    map-hom : {x y z : obj C} (f : hom y z) (g : hom x y)
            → map F (f ∘ g) ≡ map F f ∘ map F g

Functor : Category i j → Category i' j' → Set _
Functor C D = Bundle (IsFunctor {C = C}{D = D})

mk-functor : ∀ {C D} → FunctorBuilder C D → Functor C D
mk-functor b = let module B = FunctorBuilder b in record
  { parent = mk-morphism record
    { apply = B.apply
    ; map = B.map }
  ; struct = record
    { map-id = B.map-id
    ; map-hom = B.map-hom } }

private
  module functor-methods {C : Category i j}{D : Category i' j'}{k}
                         ⦃ o : Overload k (Functor C D) ⦄ where
    private
      module with-source (source : Source o) where
        private target = coerce o source
        open IsFunctor (Bundle.struct target) public
    open with-source public

open functor-methods public
