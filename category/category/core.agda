{-# OPTIONS --without-K #-}

module category.category.core where

open import level
open import function.core
open import equality.core
open import overloading

open import category.graph.core
open import category.category.builder
open import category.category.zero

open import hott.hlevel.core

record IsCategory i j (C : Category₀ i j) : Set (i ⊔ j) where
  open as-category₀ C

  field
    trunc : (x y : obj C) → h 2 (hom x y)
    left-id : {x y : obj C} (f : hom x y) → id ∘ f ≡ f
    right-id : {x y : obj C} (f : hom x y) → f ∘ id ≡ f
    assoc : {x y z w : obj C} (f : hom z w)(g : hom y z)(h : hom x y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

Category : ∀ i j → Set _
Category i j = Bundle (IsCategory i j)

cat-is-set : ∀ {i j} → Coercion (Category i j) (Set i)
cat-is-set {i}{j} = coerce-parent

cat-is-gph : ∀ {i j} → Coercion (Category i j) (Graph i j)
cat-is-gph {i}{j} = coerce-parent

cat-is-cat₀ : ∀ {i j} → Coercion (Category i j) (Category₀ i j)
cat-is-cat₀ {i}{j} = coerce-parent

cat-is-cat : ∀ {i j} → Coercion (Category i j) (Category i j)
cat-is-cat {i}{j} = coerce-self _

private
  module cat-statics {i j k}{Source : Set k}
                     ⦃ c : Coercion Source (Category i j) ⦄ where
    open Coercion c public using () renaming (coerce to cat)
  module cat-methods {i j}{C : Category₀ i j}
                     ⦃ s : Styled default (IsCategory i j C) ⦄ where
    open Styled s
    open IsCategory value public

module as-category {i j k}{Source : Set k}
                   ⦃ c : Coercion Source (Category i j) ⦄
                   (source : Source) where
  private target = coerce c source
  open as-category₀ target public
  _cat-instance = styled default (Bundle.struct target)

mk-category : ∀ {i j} → CategoryBuilder i j → Category i j
mk-category b = let module B = CategoryBuilder b in record
  { parent = mk-category₀ record
    { obj = B.obj
    ; hom = B.hom
    ; id = B.id
    ; _∘_ = B._∘_ }
  ; struct = record
    { left-id = B.left-id
    ; right-id = B.right-id
    ; assoc = B.assoc
    ; trunc = B.trunc } }

open cat-statics public
open cat-methods public
