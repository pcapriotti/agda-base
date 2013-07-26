{-# OPTIONS --type-in-type --without-K #-}

module category.groupoid.core where

open import level
open import function.core
open import equality.core
open import overloading
open import category.category.zero
open import category.category.core
open import category.graph.core
open import category.groupoid.builder
open import category.groupoid.zero

record IsGroupoid (G : Groupoid₀) : Set where
  open as-groupoid₀ G

  field
    is-cat : IsCategory (cat₀ G)
    left-inv : {x y : obj G} (f : hom x y) → inv f ∘ f ≡ id
    right-inv : {x y : obj G} (f : hom x y) → f ∘ inv f ≡ id

Groupoid : Set
Groupoid = Bundle IsGroupoid

gpd-is-set : Coercion Groupoid Set
gpd-is-set = coerce-parent

gpd-is-gph : Coercion Groupoid Graph
gpd-is-gph = coerce-parent

gpd-is-cat₀ : Coercion Groupoid Category₀
gpd-is-cat₀ = coerce-parent

gpd-is-cat : Coercion Groupoid Category
gpd-is-cat = record
  { coerce = λ G → record
    { parent = cat₀ G
    ; struct = IsGroupoid.is-cat (Bundle.struct G) } }

gpd-is-gpd₀ : Coercion Groupoid Groupoid₀
gpd-is-gpd₀ = coerce-parent

gpd-is-gpd : Coercion Groupoid Groupoid
gpd-is-gpd = coerce-self _

private
  module gpd-statics {Source : Set}
                     ⦃ c : Coercion Source Groupoid ⦄ where
    open Coercion c public using () renaming (coerce to gpd)
  module gpd-methods {G : Groupoid₀}
                     ⦃ s : Styled default (IsGroupoid G) ⦄ where
    open Styled s
    open IsGroupoid value public

module as-groupoid {Source : Set}
                   ⦃ c : Coercion Source Groupoid ⦄
                   (source : Source) where
  private target = coerce c source
  open as-category₀ target public
  _cat-instance = styled default (cat target)
  _gpd-instance = styled default (Bundle.struct target)

mk-groupoid : GroupoidBuilder → Groupoid
mk-groupoid b = let module B = GroupoidBuilder b in record
  { parent = mk-groupoid₀ record
    { obj = B.obj
    ; hom = B.hom
    ; id = B.id
    ; _∘_ = B._∘_
    ; inv = B.inv }
  ; struct = record
    { is-cat = record
      { trunc = B.trunc
      ; left-id = B.left-id
      ; right-id = B.right-id
      ; assoc = B.assoc }
    ; left-inv = B.left-inv
    ; right-inv = B.right-inv } }

open gpd-statics public
open gpd-methods public
