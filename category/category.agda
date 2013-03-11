{-# OPTIONS --without-K #-}

module category.category where

open import level using (Level ; lsuc ; _⊔_)
open import sum
open import equality.core
open import hott.hlevel

open import category.structure
import category.graph as Graph

record IsCategory {i j}(W : Graph.Graph i j) : Set (lsuc (i ⊔ j)) where
  open Graph.Graph W
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
                  → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    trunc : ∀ x y → h 2 (hom x y)

record CatStruct {i j}(X : Set i) : Set (lsuc (i ⊔ j)) where
  field is-gph : Graph.IsGraph X

  gph : Graph.Graph i j
  gph = record
    { obj = X
    ; is-gph = is-gph }

  field is-cat : IsCategory gph

record Category (i j : Level) : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    cat-st : CatStruct {i}{j} obj

  open CatStruct cat-st public
  open Graph.IsGraph is-gph public
  open IsCategory is-cat public

-- opposite category
op : ∀ {i j} → Category i j → Category i j
op C = record
  { obj = obj
  ; cat-st = record
    { is-gph = record { hom = flip hom }
    ; is-cat = record
      { id = id
      ; _∘_ = flip _∘_
      ; left-unit = right-unit
      ; right-unit = left-unit
      ; associativity = λ f g h → sym (associativity h g f)
      ; trunc = flip trunc } } }
  where
    open Category C
    open import function.core
      using (flip)

-- interface

module cat-interface {i j} ⦃ st : Structure {lsuc (i ⊔ j)}
                                            (CatStruct {i}{j}) ⦄
                           (C : Structure.Sort st) where
  open CatStruct (Structure.struct st C)
  open Graph.Graph gph
  open IsCategory is-cat

  private X = Structure.obj st C
  open import function.core
    using (Composition; Identity)

  category-comp : Composition _ _ _ _ _ _
  category-comp = record
    { U₁ = X
    ; U₂ = X
    ; U₃ = X
    ; hom₁₂ = λ x y → hom x y
    ; hom₂₃ = λ x y → hom x y
    ; hom₁₃ = λ x y → hom x y
    ; _∘_ = λ f g → f ∘ g }

  category-identity : Identity _ _
  category-identity = record
    { U = X
    ; endo = λ x → hom x x
    ; id = λ {x} → id x }

  open overloaded CatStruct C public

open Graph

cat : ∀ {i j}
    → ⦃ st : Structure {lsuc (i ⊔ j)} (CatStruct {i}{j}) ⦄
    → Structure.Sort st
    → Category i j
cat ⦃ st ⦄ X = record
  { obj = Structure.obj st X
  ; cat-st = Structure.struct st X }

graph : ∀ {i j}
      → ⦃ st : Structure {lsuc (i ⊔ j)} (IsGraph {i}{j}) ⦄
      → Structure.Sort st
      → Graph.Graph i j
graph ⦃ st ⦄ X = record
  { obj = Structure.obj st X
  ; is-gph = Structure.struct st X }

cat-cat-instance : ∀ {i j} → Structure CatStruct
cat-cat-instance {i}{j} = record
  { Sort = Category i j
  ; obj = Category.obj
  ; struct = λ C → record
    { is-gph = Category.is-gph C
    ; is-cat = Category.is-cat C } }

cat-gph-instance : ∀ {i j} → Structure IsGraph
cat-gph-instance {i}{j} = record
  { Sort = Category i j
  ; obj = Category.obj
  ; struct = Category.is-gph }

module CategoryInterface {i j} ⦃ sub : IsSubtype {lsuc (i ⊔ j)}
                                       (CatStruct {i}{j}) ⦄ where
  open import function.core public
  open IsSubtype sub
  open CatStruct structure
  open IsCategory is-cat public
    hiding (_∘_; id)
open CategoryInterface public
