{-# OPTIONS --without-K #-}

module category.category where

open import level using (Level ; lsuc ; _⊔_)
open import sum
open import function using (flip)
open import equality.core
open import hott.hlevel

open import category.structure
import category.graph as Graph

record IsCategory {i j}(X : Set i) : Set (lsuc (i ⊔ j)) where
  infixl 8 _∘_
  field
    is-gph : Graph.IsGraph {i}{j} X

  open Graph.IsGraph is-gph
  field
    id : (A : X) → hom A A
    _∘_ : {A B C : X} → hom B C → hom A B → hom A C

    left-unit : {A B : X}(f : hom A B)
              → id B ∘ f ≡ f
    right-unit : {A B : X}(f : hom A B)
               → f ∘ id A ≡ f
    associativity : {A B C D : X}
                    (f : hom A B)
                    (g : hom B C)
                    (h : hom C D)
                  → h ∘ g ∘ f ≡ h ∘ (g ∘ f)

record Category (i j : Level) : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    is-cat : IsCategory {i}{j} obj

  open IsCategory is-cat
  open Graph.IsGraph is-gph

  field
    trunc : ∀ x y → h 2 (hom x y)

  open Graph.IsGraph is-gph public
  open IsCategory is-cat public

-- opposite category
op : ∀ {i j} → Category i j → Category i j
op C = record
  { obj = obj
  ; is-cat = record
    { is-gph = record { hom = flip hom }
    ; id = id
    ; _∘_ = flip _∘_
    ; left-unit = right-unit
    ; right-unit = left-unit
    ; associativity = λ f g h → sym (associativity h g f) }
  ; trunc = flip trunc }
  where
    open Category C

-- interface

open Graph

graph : ∀ {i j}
      → ⦃ st : Structure {lsuc (i ⊔ j)} (IsCategory {i}{j}) ⦄
      → Structure.Sort st → Graph.Graph i j
graph ⦃ st ⦄ C = record
  { obj = Structure.obj st C
  ; is-gph = IsCategory.is-gph (Structure.struct st C) }

cat-cat-instance : ∀ {i j} → Structure IsCategory
cat-cat-instance {i}{j} = record
  { Sort = Category i j
  ; obj = Category.obj
  ; struct = Category.is-cat }

cat-gph-instance : ∀ {i j} → Structure IsGraph
cat-gph-instance {i}{j} = record
  { Sort = Category i j
  ; obj = Category.obj
  ; struct = λ C → Graph.is-gph (graph C) }

module CategoryInterface {i j} ⦃ sub : IsSubtype {lsuc (i ⊔ j)}
                                       (IsCategory {i}{j}) ⦄ where
  open IsSubtype sub
  open IsCategory structure public
    hiding (is-gph)

open CategoryInterface public
