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
