{-# OPTIONS --without-K #-}

module category.graph.morphism.ops where

open import function.core
open import function.overloading
open import category.graph.core
open import category.graph.morphism.core
open import category.category.zero

private
  Id : (W : Graph) → Morphism W W
  Id W = mk-morphism record
    { apply = id
    ; map = id }

gph-mor-identity : Identity
gph-mor-identity = record
  { U = Graph
  ; endo = λ W → Morphism W W
  ; id = λ {W} → Id W }

private
  Compose : {W U V : Graph}
          → Morphism U V
          → Morphism W U
          → Morphism W V
  Compose {W = W}{U = U}{V = V} f g = mk-morphism record
    { apply = λ x → apply f (apply g x)
    ; map = λ u → map f (map g u) }

gph-mor-comp : Composition
gph-mor-comp = record
  { U₁ = Graph
  ; U₂ = Graph
  ; U₃ = Graph
  ; hom₁₂ = Morphism
  ; hom₂₃ = Morphism
  ; hom₁₃ = Morphism
  ; _∘_ = Compose }

gph-cat₀ : Category₀
gph-cat₀ = mk-category₀ record
  { obj = Graph
  ; hom = Morphism
  ; id = Id
  ; _∘_ = Compose }
