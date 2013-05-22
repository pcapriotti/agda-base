{-# OPTIONS --without-K --type-in-type #-}

module category.category.core where

open import level
open import function.core
open import equality.core
open import overloading.core
open import overloading.bundle

open import category.graph.core
open import category.category.builder
open import category.category.zero

open import hott.hlevel.core

record IsCategory (C : Category₀) : Set where
  open as-category₀ C

  field
    trunc : (x y : obj C) → h 2 (hom x y)
    left-id : {x y : obj C} (f : hom x y) → id ∘ f ≡ f
    right-id : {x y : obj C} (f : hom x y) → f ∘ id ≡ f
    assoc : {x y z w : obj C} (f : hom z w)(g : hom y z)(h : hom x y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

Category : Set
Category = Bundle IsCategory

cat-is-set : Coercion Category (Set)
cat-is-set = coerce-parent

cat-is-gph : Coercion Category (Graph)
cat-is-gph = coerce-parent

cat-is-cat₀ : Coercion Category Category₀
cat-is-cat₀ = coerce-parent

cat-is-cat : Coercion Category Category
cat-is-cat = coerce-self _

private
  module cat-statics {Source : Set}
                     ⦃ c : Coercion Source Category ⦄ where
    open Coercion c public using () renaming (coerce to cat)
  module cat-methods {C : Category₀}
                     ⦃ s : Styled default (IsCategory C) ⦄ where
    open Styled s
    open IsCategory value public

module as-category {Source : Set}
                   ⦃ c : Coercion Source Category ⦄
                   (source : Source) where
  private target = coerce c source
  open as-category₀ target public
  _cat-instance = styled default (Bundle.struct target)

mk-category : CategoryBuilder → Category
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
