{-# OPTIONS --without-K #-}

module category.groupoid.core where

open import level
open import function.core using (_∘'_)
open import category.structure
open import category.category
open import category.groupoid.internal
open import equality.core using (_≡_)
open import hott.hlevel.core

record GrpdStruct {i j} (X : Set i) : Set (lsuc i ⊔ lsuc j) where
  field cat-st : CatStruct X

  cat : Category i j
  cat = record
    { obj = X
    ; cat-st = cat-st }

  field is-grpd : IsGroupoid cat

record Groupoid i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    grpd-st : GrpdStruct {i}{j} obj

  open GrpdStruct grpd-st public
  open CatStruct cat-st public

-- interface

open import category.graph

grpd-gph-instance : ∀ {i}{j} → Structure IsGraph
grpd-gph-instance {i}{j} = record
  { Sort = Groupoid i j
  ; obj = Groupoid.obj
  ; struct = Groupoid.is-gph }

grpd-cat-instance : ∀ {i}{j} → Structure CatStruct
grpd-cat-instance {i}{j} = record
  { Sort = Groupoid i j
  ; obj = Groupoid.obj
  ; struct = Groupoid.cat-st }

grpd-grpd-instance : ∀ {i}{j} → Structure GrpdStruct
grpd-grpd-instance {i}{j} = record
  { Sort = Groupoid i j
  ; obj = Groupoid.obj
  ; struct = Groupoid.grpd-st }

cat : ∀ {i j} → Groupoid i j → Category i j
cat G = GrpdStruct.cat (Groupoid.grpd-st G)

module GroupoidInterface {i}{j} ⦃ sub : IsSubtype {lsuc (i ⊔ j)}
                                                  (GrpdStruct {i}{j}) ⦄ where
  open IsSubtype sub
  open GrpdStruct structure
  open IsGroupoid is-grpd
