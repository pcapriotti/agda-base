{-# OPTIONS --without-K #-}

module category.functor.core where

open import function.core hiding (id)
open import category.category renaming (_∘_ to _⋆_)
open import category.graph hiding (Id; Compose)
import category.graph as Graph
open import category.functor.class
open import category.structure
open import level using (_⊔_)
open import equality.core using (_≡_ ; refl ; cong; sym)

record Functor {i j i' j'}
              (C : Category i j)
              (D : Category i' j')
            : Set (i ⊔ j ⊔ i' ⊔ j') where
  constructor functor

  field
    morph : Morphism (graph C) (graph D)
    is-func : IsFunctor C D morph

  open Morphism morph public
  open IsFunctor is-func public

Id : ∀ {i j}(C : Category i j) → Functor C C
Id C = functor (Graph.Id (graph C)) (id-func C)

Compose : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
          {C : Category i₁ j₁}
          {D : Category i₂ j₂}
          {E : Category i₃ j₃}
        → Functor D E
        → Functor C D
        → Functor C E
Compose {C = C} {D} {E} (functor m₁ f₁) (functor m₂ f₂)
  = functor (m₁ ∘ m₂) (comp-func C D E m₁ m₂ f₁ f₂)

functor-comp : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
               → Composition _ _ _ _ _ _
functor-comp {i₁}{j₁}{i₂}{j₂}{i₃}{j₃} = record
  { U₁ = Category i₁ j₁
  ; U₂ = Category i₂ j₂
  ; U₃ = Category i₃ j₃
  ; hom₁₂ = Functor
  ; hom₂₃ = Functor
  ; hom₁₃ = Functor
  ; _∘_ = Compose }

Const : ∀ {i j i' j'}(C : Category i j){D : Category i' j'}
      → (X : obj D) → Functor C D
Const C {D} X = record
  { morph = record
    { apply = λ _ → X
    ; map = λ _ → id }
  ; is-func = record
    { map-id = λ _ → refl
    ; map-hom = λ _ _ → sym (right-unit _) } }
  where
    open cat-interface D
