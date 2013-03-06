{-# OPTIONS --without-K #-}

module category.category where

open import level using (Level ; lsuc ; _⊔_)
open import sum
open import function using (flip)
open import equality.core
open import hott.hlevel

import category.graph as Graph

record IsCategory {i j}(graph : Graph.Graph i j) : Set (i ⊔ j) where
  infixl 8 _∘_
  open Graph.Graph graph
  field
    id : (A : obj) → hom A A
    _∘_ : {A B C : obj} → hom B C → hom A B → hom A C

    left-unit : {A B : obj}(f : hom A B)
              → id B ∘ f ≡ f
    right-unit : {A B : obj}(f : hom A B)
               → f ∘ id A ≡ f
    associativity : {A B C D : obj}
                    (f : hom A B)
                    (g : hom B C)
                    (h : hom C D)
                  → h ∘ g ∘ f ≡ h ∘ (g ∘ f)

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
    ; is-gph = record { hom = flip hom } }
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
