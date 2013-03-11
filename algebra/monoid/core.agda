{-# OPTIONS --without-K #-}

module algebra.monoid.core where

open import level
open import category.graph.core
open import category.category
open import category.structure
open import sets.unit
open import hott.hlevel.core

private
  -- a graph on a single node
  shift : ∀ {i} (X : Set i) → IsGraph ⊤
  shift X = record { hom = λ _ _ → X }

record MonStruct {i} (X : Set i) : Set (lsuc i) where
  field
    is-mon : IsCategory record
      { obj = ⊤
      ; is-gph = shift X }

record Monoid i : Set (lsuc i) where
  field
    carrier : Set i
    mon-st : MonStruct carrier

  cat-st : CatStruct ⊤
  cat-st = record
    { is-gph = shift carrier
    ; is-cat = MonStruct.is-mon mon-st }

  as-category : Category lzero i
  as-category = record
    { obj = ⊤
    ; cat-st = cat-st }

  open cat-interface as-category

-- interface

open import algebra.structure public

mon-algst-instance : ∀ {i} → AlgStruct (Monoid i)
mon-algst-instance {i} = record
  { carrier = Monoid.carrier }

mon-mon-instance : ∀ {i} → Structure (MonStruct {i})
mon-mon-instance {i} = record
  { Sort = Monoid i
  ; obj = Monoid.carrier
  ; struct = Monoid.mon-st }

mon-cat-instance : ∀ {i} → Structure CatStruct
mon-cat-instance {i} = record
  { Sort = Monoid i
  ; obj = λ _ → ⊤
  ; struct = Monoid.cat-st }

module mon-interface {i}
         ⦃ st : Structure {lsuc i} (MonStruct {i}) ⦄
         (X : Structure.Sort st)
       = overloaded MonStruct ⦃ st ⦄ X

module MonoidInterface {i}
          ⦃ sub : IsSubtype {lsuc i} (MonStruct {i}) ⦄ where
  open IsSubtype sub
  open MonStruct structure

  private
    C : Set i
    C = Structure.obj st X

  unit : C
  unit = IsCategory.id is-mon tt

  _⋆_ : C → C → C
  x ⋆ y = IsCategory._∘_ is-mon y x

open MonoidInterface public
