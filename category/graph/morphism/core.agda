{-# OPTIONS --without-K #-}

module category.graph.morphism.core {i j i' j'} where

open import level
open import function.overloading
open import overloading.core
open import category.graph.core
open import category.graph.morphism.builder

record IsMorphism {W : Graph i j}
                  {U : Graph i' j'}
                  (f : obj W → obj U) : Set (i ⊔ j ⊔ i' ⊔ j') where
  open as-graph W
  open as-graph U
  field
    map : {x y : obj W} → hom x y → hom (apply f x) (apply f y)

Morphism : (W : Graph i j) (U : Graph i' j') → Set _
Morphism W U = Bundle (IsMorphism {W = W}{U = U})

mor-is-fun : {W : Graph i j}{U : Graph i' j'}
           → Overload _ (obj W → obj U)
mor-is-fun {W}{U} = record
  { Source = Morphism W U
  ; coerce = Bundle.parent }

mor-is-mor : {W : Graph i j}{U : Graph i' j'}
           → Overload _ (Morphism W U)
mor-is-mor {W}{U} = overload-self (Morphism W U)

private
  module mor-methods {k}{W : Graph i j}{U : Graph i' j'}
                     ⦃ o : Overload k (Morphism W U) ⦄ where
    open Overload o public using ()
      renaming (coerce to morphism)
    private
      module with-arg (f : Source o) where
        open IsMorphism (Bundle.struct (coerce o f)) public
    open with-arg public

mk-morphism : ∀ {W U} → MorphismBuilder W U → Morphism W U
mk-morphism b = let module B = MorphismBuilder b in record
  { parent = B.apply
  ; struct = record { map = B.map } }

open mor-methods public
