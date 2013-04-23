{-# OPTIONS --without-K #-}

module category2.functor.core {i j i' j'} where

open import level
open import equality.core
open import function.core
open import overloading
open import category2.category.core
open import category2.graph.core
open import category2.graph.morphism

record IsFunctor {C : Category i j}
                 {D : Category i' j'}
                 (F : Morphism (graph C) (graph D)) : Set (i ⊔ j ⊔ j') where
  open as-category C
  open as-category D
  open morphisms C D

  field
    map-id : {x : obj C} → map F (id {X = x}) ≡ id
    map-hom : {x y z : obj C} (f : hom y z) (g : hom x y)
            → map F (f ∘ g) ≡ map F f ∘ map F g

Functor : Category i j → Category i' j' → Set _
Functor C D = Bundle (IsFunctor {C = C}{D = D})

functor-exp : Exponential _ (Category i j) (Category i' j')
functor-exp = exponential Functor

module functors {k₁ k₂} ⦃ o₁ : Overload k₁ (Category i j) ⦄
                       ⦃ o₂ : Overload k₂ (Category i' j') ⦄
                       (C' : Source o₁)
                       (D' : Source o₂) where
  C = coerce o₁ C'
  D = coerce o₂ D'

  _instance : ExpOverload _ (Category i j) (Category i' j')
  _instance = record
    { X = C
    ; Y = D
    ; o = overload-self (Functor C D) }

  _mor-instance : ExpOverload _ (Graph i j) (Graph i' j')
  _mor-instance = record
    { X = graph C
    ; Y = graph D
    ; o = record
      { Source = Functor C D
      ; coerce = Bundle.parent } }

  _func-instance : ExpOverload _ (Set i) (Set i')
  _func-instance = record
    { X = obj C
    ; Y = obj D
    ; o = record
      { Source = Functor C D
      ; coerce = λ F → Bundle.parent (Bundle.parent F) } }

private
  module functor-methods {k} ⦃ eo : ExpOverload k (Category i j) (Category i' j') ⦄ where
    open ExpOverload eo
    private
      module with-arg (F : Functor X Y) where
        open IsFunctor (Bundle.struct F) public
    open with-arg public

open functor-methods public
