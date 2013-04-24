{-# OPTIONS --without-K #-}

module category2.graph.core where

open import level
open import sum
open import overloading

record IsGraph i j (X : Set i) : Set (i ⊔ lsuc j) where
  field
    hom : X → X → Set j

Graph : ∀ i j → Set _
Graph i j = Bundle (IsGraph i j)

gph-is-set : ∀ {i j} → Overload _ (Set i)
gph-is-set {i}{j} = overload-parent (IsGraph i j)

gph-is-gph : ∀ {i j} → Overload _ (Graph i j)
gph-is-gph {i}{j} = overload-self (Graph i j)

private
  module graph-statics {i j k} ⦃ o : Overload k (Graph i j) ⦄ where
    open Overload o public using () renaming (coerce to graph)

    private
      module with-source (source : Source o) where
        private target = coerce o source
        open IsGraph (Bundle.struct target)

        open Bundle target public using ()
          renaming (parent to obj)

        total : Set _
        total = Σ (obj × obj) λ { (x , y) → hom x y }
    open with-source public

  module graph-methods {i j k} ⦃ o : OverloadInstance k default (Graph i j) ⦄ where
    open OverloadInstance o
    open IsGraph (Bundle.struct target) public

module as-graph {i j k} ⦃ o : Overload k (Graph i j) ⦄
                (source : Source o) where
  open overload default (Graph i j) source public

record GraphBuilder i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    hom : obj → obj → Set j

mk-graph : ∀ {i j} → GraphBuilder i j → Graph i j
mk-graph b = let open GraphBuilder b in record
  { parent = obj
  ; struct = record { hom = hom } }

open graph-statics public
open graph-methods public

