{-# OPTIONS --without-K #-}

module category.functor.core where

open import category.category renaming (_∘_ to _⋆_)
import category.graph as Graph
open import category.functor.class
open import level using (_⊔_)
open import equality.core using (_≡_ ; refl ; cong; sym)

open Category using (graph; is-cat)

record Functor {i j i' j'}
              (C : Category i j)
              (D : Category i' j')
            : Set (i ⊔ j ⊔ i' ⊔ j') where
  constructor functor

  field
    morph : Graph.Morphism (graph C) (graph D)
    is-func : IsFunctor (is-cat C) (is-cat D) morph

  open Graph.Morphism morph public
  open IsFunctor is-func public

Id : ∀ {i j}(C : Category i j) → Functor C C
Id C = functor (Graph.Id (graph C))
               (id-func (is-cat C))

_∘_ : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
          {C : Category i₁ j₁}
          {D : Category i₂ j₂}
          {E : Category i₃ j₃}
        → Functor D E
        → Functor C D
        → Functor C E
_∘_ {C = C} {D} {E} (functor m₁ f₁) (functor m₂ f₂)
  = functor (Graph._∘_ m₁ m₂) (comp-func m₁ m₂ f₁ f₂)
infixl 5 _∘_

Const : ∀ {i j i' j'}(C : Category i j){D : Category i' j'}
      → (X : obj D) → Functor C D
Const C {D} X = record
  { morph = record
    { apply = λ _ → X
    ; map = λ _ → id X }
  ; is-func = record
    { map-id = λ _ → refl
    ; map-hom = λ _ _ → sym (right-unit _) } }