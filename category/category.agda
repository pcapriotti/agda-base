{-# OPTIONS --without-K #-}

module category.category where

open import level using (Level ; lsuc ; _⊔_)
open import sum
open import function using (flip)
open import equality.core
open import hott.hlevel

import category.graph as Graph
open import category.class

record Category (i j : Level) : Set (lsuc (i ⊔ j)) where
  field
    graph : Graph.Graph i j
    is-cat : IsCategory graph

  open Graph.Graph graph
  open IsCategory is-cat

  field
    trunc : ∀ x y → h 2 (hom x y)

  mor : Set (i ⊔ j)
  mor = Σ (obj × obj) (uncurry hom)

  open Graph.Graph graph public
  open IsCategory is-cat public

-- opposite category
op : ∀ {i j} → Category i j → Category i j
op C = record
  { graph = record
    { obj = obj
    ; hom = flip hom }
  ; is-cat = record
    { id = id
    ; _∘_ = flip _∘_
    ; left-unit = right-unit
    ; right-unit = left-unit
    ; associativity = λ f g h → sym (associativity h g f) }
  ; trunc = flip trunc }
  where
    open Category C

-- interface

open Category public using (obj; mor; trunc)
private
  module Interface {i j} ⦃ C : Category i j ⦄ where
    open Category C using (is-cat)
    open Category C public using (hom)
    open IsCategory is-cat public
open Interface public
