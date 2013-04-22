{-# OPTIONS --without-K #-}

module category2.graph.morphism where

open import level
open import overloading
open import category2.graph.core

record IsMorphism {i j i' j'}
                  {W : Graph i j}
                  {U : Graph i' j'}
                  (f : obj W → obj U) : Set (i ⊔ j ⊔ i' ⊔ j') where
  open as-graph W
  open as-graph U
  field
    map : {x y : obj W} → hom x y → hom (f x) (f y)

Morphism : ∀ {i j i' j'} (W : Graph i j) (U : Graph i' j') → Set _
Morphism {i}{j}{i'}{j'} W U = Bundle (IsMorphism {W = W}{U = U})

private
  module properties {i j i' j'}
                    {W : Graph i j}
                    {U : Graph i' j'} where
    open as-graph W
    open as-graph U

    mor-is-mor : Overload _ (Morphism W U)
    mor-is-mor = overload-self (Morphism W U)

    private
      module mor-statics {i} ⦃ o : Overload i (Morphism W U) ⦄ where
        open Overload o public using () renaming (coerce to graph-morphism)

        apply : Source o → obj W → obj U
        apply f = Bundle.parent (coerce o f)

        map : (f : Source o) → {x y : obj W} → hom x y → hom (apply f x) (apply f y)
        map f = IsMorphism.map (Bundle.struct (coerce o f))

    record MorphismBuilder : Set (i ⊔ j ⊔ i' ⊔ j') where
      field
        apply : obj W → obj U
        map : {x y : obj W} → hom x y → hom (apply x) (apply y)

    mk-graph-morphism : MorphismBuilder → Morphism W U
    mk-graph-morphism b = let module B = MorphismBuilder b in record
      { parent = B.apply
      ; struct = record { map = B.map } }

    open mor-statics public
open properties public
