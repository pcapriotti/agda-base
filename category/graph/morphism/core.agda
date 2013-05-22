{-# OPTIONS --without-K --type-in-type #-}

module category.graph.morphism.core where

open import level
open import function.overloading
open import overloading.bundle
open import overloading.core
open import category.graph.core
open import category.graph.morphism.builder

record IsMorphism {W U : Graph}
                  (f : obj W → obj U) : Set where
  open as-graph W
  open as-graph U
  field
    map : {x y : obj W} → hom x y → hom (apply f x) (apply f y)

Morphism : (W : Graph) (U : Graph) → Set
Morphism W U = Bundle (IsMorphism {W = W}{U = U})

mor-is-fun : {W : Graph}{U : Graph}
           → Coercion (Morphism W U) (obj W → obj U)
mor-is-fun {W}{U} = coerce-parent

mor-is-mor : {W : Graph}{U : Graph}
           → Coercion (Morphism W U) (Morphism W U)
mor-is-mor {W}{U} = coerce-self _

private
  module mor-methods {W : Graph}{U : Graph} {Source : Set}
                     ⦃ c : Coercion Source (Morphism W U) ⦄ where
    open Coercion c public using ()
      renaming (coerce to graph-morphism)
  module mor-explicits {W : Graph}{U : Graph} {Source : Set}
                       ⦃ c : Coercion Source (Morphism W U) ⦄
                       (source : Source) where
    private target = coerce c source
    open IsMorphism (Bundle.struct target) public

mk-morphism : ∀ {W U} → MorphismBuilder W U → Morphism W U
mk-morphism b = let module B = MorphismBuilder b in record
  { parent = B.apply
  ; struct = record { map = B.map } }

open mor-methods public
open mor-explicits public
