{-# OPTIONS --without-K #-}

module category2.category.core where

open import level
open import function.core
open import equality.core
open import overloading

open import category2.graph.core
open import category2.category.builder
open import category2.category.zero

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

cat-is-set : ∀ {i j} → Overload _ (Set i)
cat-is-set {i}{j} = overload-parent (IsCategory i j)

cat-is-gph : ∀ {i j} → Overload _ (Graph i j)
cat-is-gph {i}{j} = overload-parent (IsCategory i j)

cat-is-cat₀ : ∀ {i j} → Overload _ (Category₀ i j)
cat-is-cat₀ {i}{j} = overload-parent (IsCategory i j)

cat-is-cat : ∀ {i j} → Overload _ (Category i j)
cat-is-cat {i}{j} = overload-self (Category i j)

private
  module cat-statics {i j k} ⦃ o : Overload k (Category i j) ⦄ where
    open Overload o public using () renaming (coerce to cat)
  module cat-methods {i j k} ⦃ o : OverloadInstance k default (Category i j) ⦄ where
    open OverloadInstance o
    open IsCategory (Bundle.struct target) public

module as-category {i j k} ⦃ o : Overload k (Category i j) ⦄
                    (source : Source o) where
  private target = coerce o source
  open overload default (Category₀ i j) target public
    renaming (_instance to _parent-instance)
  open overload default (Category i j) target public

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
