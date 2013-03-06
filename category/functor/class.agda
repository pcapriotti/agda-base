{-# OPTIONS --without-K #-}

module category.functor.class where

open import level
open import equality.core
open import equality.reasoning
open import category.category
  using (IsCategory; module IsCategory)
import category.graph as Graph
open Graph
  using ()
  renaming (_∘_ to _⋆_)

private
  module Interface {i j}{G : Graph.Graph i j}
                   ⦃ c : IsCategory G ⦄ where
    open IsCategory c public

open Interface
open Graph.Graph

record IsFunctor {i j i' j'}
                 {C : Graph.Graph i j}
                 {D : Graph.Graph i' j'}
                 (cC : IsCategory C)
                 (cD : IsCategory D)
                 (m : Graph.Morphism C D)
               : Set (i ⊔ j ⊔ i' ⊔ j') where
  constructor is-functor

  open Graph.Morphism m
    renaming (apply to F)

  field
    map-id : (X : obj C)
           → map (id X) ≡ id (F X)
    map-hom : {X Y Z : obj C}
              (f : hom C X Y)(g : hom C Y Z)
            → map (g ∘ f) ≡ map g ∘ map f

id-func : ∀ {i j}{C : Graph.Graph i j}(c : IsCategory C)
        → IsFunctor c c (Graph.Id C)
id-func _ = record
  { map-id = λ _ → refl
  ; map-hom = λ _ _ → refl }

comp-func : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
            {C : Graph.Graph i₁ j₁}
            {D : Graph.Graph i₂ j₂}
            {E : Graph.Graph i₃ j₃}
            {cC : IsCategory C}
            {cD : IsCategory D}
            {cE : IsCategory E}
            (F : Graph.Morphism D E)
            (G : Graph.Morphism C D)
          → IsFunctor cD cE F
          → IsFunctor cC cD G
          → IsFunctor cC cE (F ⋆ G)
comp-func {cC = cC} {cD = cD} {cE = cE} F G f-func g-func = record
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
    open Graph.Morphism
    open IsFunctor
