{-# OPTIONS --without-K #-}

module category.graph.core where

open import level
open import sum
open import overloading

record IsGraph i j (X : Set i) : Set (i ⊔ lsuc j) where
  field
    hom : X → X → Set j

Graph : ∀ i j → Set _
Graph i j = Bundle (IsGraph i j)

gph-is-set : ∀ {i j} → Coercion (Graph i j) (Set i)
gph-is-set {i}{j} = coerce-parent

gph-is-gph : ∀ {i j} → Coercion (Graph i j) (Graph i j)
gph-is-gph {i}{j} = coerce-self _

private
  module graph-statics {i j k}{Source : Set k}
                       ⦃ c : Coercion Source (Graph i j) ⦄ where
    open Coercion c public using () renaming (coerce to graph)

    private
      module with-source (source : Source) where
        private target = coerce c source
        open IsGraph (Bundle.struct target)

        open Bundle target public using ()
          renaming (parent to obj)

        total : Set _
        total = Σ (obj × obj) λ { (x , y) → hom x y }
    open with-source public
  module graph-methods {i j}{X : Set i}
                       ⦃ s : Styled default (IsGraph i j X) ⦄ where
    open Styled s
    open IsGraph value public

module as-graph {i j k} {Source : Set k}
                ⦃ c : Coercion Source (Graph i j) ⦄
                (source : Source) where
  private target = coerce c source
  _graph-instance = styled default (Bundle.struct target)

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

module example {i}{j} (W : Graph i j)(U : Graph i j) where
  open as-graph W

  test : obj W → Set j
  test x = hom x x
