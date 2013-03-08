{-# OPTIONS --without-K #-}

module category.graph.morphism where

open import level
open import category.graph.core
open import function.core

IsMorphism : ∀ {i j i' j'}{A : Graph i j}{B : Graph i' j'}
           → (f : obj A → obj B) → Set _
IsMorphism {A = A}{B = B} f =
  ∀ {x y} → hom A x y → hom B (f x) (f y)

record Morphism {i j i' j'}
                (A : Graph i j)
                (B : Graph i' j')
              : Set (i ⊔ i' ⊔ j ⊔ j') where
  constructor morphism
  field
    apply : obj A → obj B
    map : ∀ {x y} → hom A x y → hom B (apply x) (apply y)

open Morphism

Id : ∀ {i j} (G : Graph i j) → Morphism G G
Id _ = morphism (λ x → x) (λ f → f)

Compose : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
          {G : Graph i₁ j₁}
          {H : Graph i₂ j₂}
          {K : Graph i₃ j₃}
        → Morphism H K
        → Morphism G H
        → Morphism G K
Compose F G = record
  { apply = λ x → apply F (apply G x)
  ; map = λ f → map F (map G f) }

gmorphism-comp : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
               → Composition _ _ _ _ _ _
gmorphism-comp {i₁}{j₁}{i₂}{j₂}{i₃}{j₃} = record
  { U₁ = Graph i₁ j₁
  ; U₂ = Graph i₂ j₂
  ; U₃ = Graph i₃ j₃
  ; hom₁₂ = Morphism
  ; hom₂₃ = Morphism
  ; hom₁₃ = Morphism
  ; _∘_ = Compose }
