{-# OPTIONS --without-K #-}

module category.groupoid.core where

open import level
open import function.core using (_∘'_)
open import category.structure
open import category.graph
  using (IsGraph; module IsGraph)
open import category.category
  using (Category; IsCategory; module IsCategory)
open import equality.core using (_≡_)
open import hott.hlevel.core

record IsGroupoid {i j} (X : Set i) : Set (lsuc (i ⊔ j)) where
  infix 8 _⁻¹
  field
    is-cat : IsCategory {i}{j} X

  open IsCategory is-cat
  open IsGraph is-gph

  field
    -- structure
    _⁻¹ : {A B : X} → hom A B → hom B A

    -- laws
    left-inverse : {A B : X}(f : hom A B)
                 → (f ⁻¹) ∘ f ≡ id A

    right-inverse : {A B : X}(f : hom A B)
                  → f ∘ (f ⁻¹) ≡ id B

record Groupoid i j : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    is-grpd : IsGroupoid {i}{j} obj

  open IsGroupoid is-grpd
  open IsCategory is-cat
  open IsGraph is-gph

  field
    trunc : (A B : obj) → h 2 (hom A B)

-- interface

grpd-gph-instance : ∀ {i}{j} → Structure IsGraph
grpd-gph-instance {i}{j} = record
  { Sort = Groupoid i j
  ; obj = Groupoid.obj
  ; struct = IsCategory.is-gph
           ∘' IsGroupoid.is-cat
           ∘' Groupoid.is-grpd }

grpd-cat-instance : ∀ {i}{j} → Structure IsCategory
grpd-cat-instance {i}{j} = record
  { Sort = Groupoid i j
  ; obj = Groupoid.obj
  ; struct = IsGroupoid.is-cat ∘' Groupoid.is-grpd }

grpd-grpd-instance : ∀ {i}{j} → Structure IsGroupoid
grpd-grpd-instance {i}{j} = record
  { Sort = Groupoid i j
  ; obj = Groupoid.obj
  ; struct = Groupoid.is-grpd }

cat : ∀ {i j} → Groupoid i j → Category i j
cat G = record
  { obj = Groupoid.obj G
  ; is-cat = IsGroupoid.is-cat (Groupoid.is-grpd G)
  ; trunc = Groupoid.trunc G }

module GroupoidInterface {i}{j} ⦃ sub : IsSubtype {lsuc (i ⊔ j)}
                                                  (IsGroupoid {i}{j}) ⦄ where
  open IsSubtype sub
  open IsGroupoid structure public
    hiding (is-cat)
