{-# OPTIONS --without-K #-}

module category.functor.class where

open import level
open import equality.core
open import equality.reasoning
open import category.category
open import category.graph
  renaming (_∘_ to _⋆_)

record IsFunctor {i j i' j'}
                 (C : Category i j)
                 (D : Category i' j')
                 (m : Morphism (graph C) (graph D))
               : Set (i ⊔ j ⊔ i' ⊔ j') where
  constructor is-functor

  open cat-interface C
  open cat-interface D
  open Morphism m
    renaming (apply to F)

  field
    map-id : (X : obj C)
           → map (id X) ≡ id (F X)
    map-hom : {X Y Z : obj C}
              (f : hom C X Y)(g : hom C Y Z)
            → map (g ∘ f) ≡ map g ∘ map f

id-func : ∀ {i j}(C : Category i j)
        → IsFunctor C C (Id (graph C))
id-func _ = record
  { map-id = λ _ → refl
  ; map-hom = λ _ _ → refl }

comp-func : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
            (C : Category i₁ j₁)
            (D : Category i₂ j₂)
            (E : Category i₃ j₃)
            (F : Morphism (graph D) (graph E))
            (G : Morphism (graph C) (graph D))
          → IsFunctor D E F
          → IsFunctor C D G
          → IsFunctor C E (F ⋆ G)
comp-func C D E F G f-func g-func = record
  { map-id = λ X → begin
        map F (map G (id _))
      ≡⟨ cong (map F) (map-id g-func X) ⟩
        map F (id _)
      ≡⟨ map-id f-func _ ⟩
        id _
      ∎
  ; map-hom = λ f g → begin
        map F (map G (g ∘ f))
      ≡⟨ cong (map F) (map-hom g-func f g) ⟩
        map F (map G g ∘ map G f)
      ≡⟨ map-hom f-func (map G f) (map G g) ⟩
        map F (map G g) ∘ map F (map G f)
      ∎ }
  where
    open ≡-Reasoning
    open Morphism
    open IsFunctor

    open cat-interface C
    open cat-interface D
    open cat-interface E
