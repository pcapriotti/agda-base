{-# OPTIONS --without-K #-}

module category.graph.core where

open import level
open import sum
open import category.structure

record IsGraph {i j} (X : Set i) : Set (lsuc (i ⊔ j)) where
  field
    hom : X → X → Set j

record Graph i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    is-gph : IsGraph {i}{j} obj

  open IsGraph is-gph public

module GraphInterface {i j}
                      ⦃ st : Structure {lsuc (i ⊔ j)}
                                       (IsGraph {i}{j}) ⦄ where
  module S = Structure st
  obj : S.Sort → Set _
  obj X = S.obj X

  hom : (X : S.Sort) → obj X → obj X → Set _
  hom X = IsGraph.hom (S.struct X)

  total : S.Sort → Set (i ⊔ j)
  total X = Σ (obj X × obj X) (uncurry (hom X))

open GraphInterface public

gph-gph-instance : ∀ {i j} → Structure IsGraph
gph-gph-instance {i}{j} = record
  { Sort = Graph i j
  ; obj = Graph.obj
  ; struct = Graph.is-gph }

-- obj : ∀ {i j} → ⦃ st : Structure {lsuc (i ⊔ j)} (IsGraph {i}{j}) ⦄
--     → Structure.Sort st → Set _
-- obj ⦃ st ⦄ X = Structure.obj st X

IsMorphism : ∀ {i j i' j'}{A : Graph i j}{B : Graph i' j'}
           → (f : obj A → obj B) → Set _
IsMorphism {A = A}{B = B} f =
  ∀ {x y} → hom A x y → hom B (f x) (f y)
  where
    open overloaded IsGraph A
    open overloaded IsGraph B

record Morphism {i j i' j'}
                (A : Graph i j)
                (B : Graph i' j')
              : Set (i ⊔ i' ⊔ j ⊔ j') where
  constructor morphism
  open overloaded IsGraph A
  open overloaded IsGraph B
  field
    apply : obj A → obj B
    map : ∀ {x y} → hom A x y → hom B (apply x) (apply y)

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
