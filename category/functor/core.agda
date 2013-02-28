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
Id C = record
  { morph = record
    { apply = λ X → X
    ; map = λ f → f }
  ; is-func = record
    { map-id = λ _ → refl
    ; map-hom = λ _ _ → refl } }

_∘_ : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
          {C : Category i₁ j₁}
          {D : Category i₂ j₂}
          {E : Category i₃ j₃}
        → Functor D E
        → Functor C D
        → Functor C E
_∘_ {C = C} {D} {E} F G = record
  { morph = record
    { apply = λ X → apply F (apply G X)
    ; map = λ f → map F (map G f) }
  ; is-func = record
    { map-id = λ X → begin
          map F (map G (id _))
        ≡⟨ cong (map F) (map-id G X) ⟩
          map F (id _)
        ≡⟨ map-id F _ ⟩
          id _
        ∎
    ; map-hom = λ f g → begin
          map F (map G (g ⋆ f))
        ≡⟨ cong (map F) (map-hom G f g) ⟩
          map F (map G g ⋆ map G f)
        ≡⟨ map-hom F (map G f) (map G g) ⟩
          map F (map G g) ⋆ map F (map G f)
        ∎ } }
  where
    open import equality.reasoning
    open ≡-Reasoning

    open Functor
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
