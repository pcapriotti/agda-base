{-# OPTIONS --without-K #-}

module category.graph.morphism.ops where

open import function.core
open import function.overloading
open import category.graph.core
open import category.graph.morphism.core
open import category.category.zero

private
  Id : ∀ {i j} (W : Graph i j) → Morphism W W
  Id W = mk-morphism record
    { apply = id
    ; map = id }

gph-mor-identity : ∀ {i j} → Identity _ _
gph-mor-identity {i}{j} = record
  { U = Graph i j
  ; endo = λ W → Morphism W W
  ; id = λ {W} → Id W }

private
  Compose : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
          → {W : Graph i₁ j₁}
          → {U : Graph i₂ j₂}
          → {V : Graph i₃ j₃}
          → Morphism U V
          → Morphism W U
          → Morphism W V
  Compose {W = W}{U = U}{V = V} f g = mk-morphism record
    { apply = λ x → apply f (apply g x)
    ; map = λ u → map f (map g u) }

gph-mor-comp : ∀ {i₁ j₁ i₂ j₂ i₃ j₃} → Composition _ _ _ _ _ _
gph-mor-comp {i₁}{j₁}{i₂}{j₂}{i₃}{j₃} = record
  { U₁ = Graph i₁ j₁
  ; U₂ = Graph i₂ j₂
  ; U₃ = Graph i₃ j₃
  ; hom₁₂ = Morphism
  ; hom₂₃ = Morphism
  ; hom₁₃ = Morphism
  ; _∘_ = Compose }

gph-cat₀ : ∀ {i j} → Category₀ _ _
gph-cat₀ {i}{j} = mk-category₀ record
  { obj = Graph i j
  ; hom = Morphism
  ; id = Id
  ; _∘_ = Compose }
