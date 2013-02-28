{-# OPTIONS --without-K #-}

module category.functor.class where

open import level
open import equality.core
open import category.class
open import category.graph as Graph

private
  module Interface {i j}{G : Graph.Graph i j}
                   ⦃ c : IsCategory G ⦄ where
    open IsCategory c public

record IsFunctor {i j i' j'}
                 {C : Graph i j}
                 {D : Graph i' j'}
                 (cC : IsCategory C)
                 (cD : IsCategory D)
                 (m : Graph.Morphism C D)
               : Set (i ⊔ j ⊔ i' ⊔ j') where
  constructor is-functor

  open Graph.Graph
  open Graph.Morphism m
    renaming (apply to F)
  open Interface

  field
    map-id : (X : obj C)
           → map (id X) ≡ id (F X)
    map-hom : {X Y Z : obj C}
              (f : hom C X Y)(g : hom C Y Z)
            → map (g ∘ f) ≡ map g ∘ map f
