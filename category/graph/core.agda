{-# OPTIONS --without-K --type-in-type #-}

module category.graph.core where

open import level
open import sum
open import overloading.core
open import overloading.bundle

record IsGraph (X : Set) : Set where
  field
    hom : X → X → Set

Graph : Set
Graph = Bundle IsGraph

gph-is-set : Coercion Graph Set
gph-is-set = coerce-parent

gph-is-gph : Coercion Graph Graph
gph-is-gph = coerce-self _

private
  module graph-statics {Source : Set}
                       ⦃ c : Coercion Source (Graph) ⦄ where
    open Coercion c public using () renaming (coerce to graph)

    private
      module with-source (source : Source) where
        private target = coerce c source
        open IsGraph (Bundle.struct target)

        open Bundle target public using ()
          renaming (parent to obj)

        total : Set
        total = Σ (obj × obj) λ { (x , y) → hom x y }
    open with-source public
  module graph-methods {X : Set}
                       ⦃ s : Styled default (IsGraph X) ⦄ where
    open Styled s
    open IsGraph value public

module as-graph {Source : Set}
                ⦃ c : Coercion Source (Graph) ⦄
                (source : Source) where
  private target = coerce c source
  _graph-instance = styled default (Bundle.struct target)

record GraphBuilder : Set where
  field
    obj : Set
    hom : obj → obj → Set

mk-graph : GraphBuilder → Graph
mk-graph b = let open GraphBuilder b in record
  { parent = obj
  ; struct = record { hom = hom } }

open graph-statics public
open graph-methods public
