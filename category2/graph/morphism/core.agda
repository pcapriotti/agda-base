{-# OPTIONS --without-K #-}

module category2.graph.morphism.core {i j i' j'} where

open import level
open import overloading.core
open import overloading.function
open import category2.graph.core
open import category2.graph.morphism.builder

record IsMorphism {W : Graph i j}
                  {U : Graph i' j'}
                  (f : obj W → obj U) : Set (i ⊔ j ⊔ i' ⊔ j') where
  open as-graph W
  open as-graph U
  open functions W U
  field
    map : {x y : obj W} → hom x y → hom (apply f x) (apply f y)

Morphism : (W : Graph i j) (U : Graph i' j') → Set _
Morphism W U = Bundle (IsMorphism {W = W}{U = U})

graph-exp : Exponential _ (Graph i j) (Graph i' j')
graph-exp = exponential Morphism

module morphisms {k k'}
                 ⦃ o₁ : Overload k (Graph i j) ⦄
                 ⦃ o₂ : Overload k' (Graph i' j') ⦄
                 (W' : Source o₁)(U' : Source o₂) where
  W = coerce o₁ W'
  U = coerce o₂ U'

  _instance : ExpOverload _ (Graph i j) (Graph i' j')
  _instance = record
    { X = W
    ; Y = U
    ; o = overload-self (Morphism W U) }

  _func-instance : ExpOverload _ (Set i) (Set i')
  _func-instance = record
    { X = obj W
    ; Y = obj U
    ; o = record
      { Source = Morphism W U
      ; coerce = Bundle.parent } }

private
  module mor-methods {k} ⦃ eo : ExpOverload k (Graph i j) (Graph i' j') ⦄ where
    open ExpOverload eo
    private
      module with-arg (f : Morphism X Y) where
        open IsMorphism (Bundle.struct f) public
    open with-arg public

mk-graph-morphism : ∀ {W U} → MorphismBuilder W U → Morphism W U
mk-graph-morphism b = let module B = MorphismBuilder b in record
  { parent = B.apply
  ; struct = record { map = B.map } }

open mor-methods public
