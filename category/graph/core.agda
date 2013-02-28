{-# OPTIONS --without-K #-}

module category.graph.core where

open import level
open import sum

record Graph i j : Set (lsuc (i ⊔ j)) where
  constructor graph
  field
    obj : Set i
    hom : obj → obj → Set j

  total : Set (i ⊔ j)
  total = Σ (obj × obj) (uncurry hom)

record Morphism {i j i' j'}
                (G : Graph i j)
                (H : Graph i' j')
              : Set (i ⊔ i' ⊔ j ⊔ j') where
  constructor morphism
  open Graph
  field
    apply : obj G → obj H
    map : ∀ {x y} → hom G x y → hom H (apply x) (apply y)

open Morphism

Id : ∀ {i j} (G : Graph i j) → Morphism G G
Id _ = morphism (λ x → x) (λ f → f)

_∘_ : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
      {G : Graph i₁ j₁}
      {H : Graph i₂ j₂}
      {K : Graph i₃ j₃}
    → Morphism H K
    → Morphism G H
    → Morphism G K
F ∘ G = record
  { apply = λ x → apply F (apply G x)
  ; map = λ f → map F (map G f) }
