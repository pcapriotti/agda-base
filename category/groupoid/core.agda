{-# OPTIONS --without-K #-}

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

record IsGroupoid i j (G : Groupoid₀ i j) : Set (i ⊔ j) where
  open as-groupoid₀ G

  field
    is-cat : IsCategory i j (cat₀ G)
    left-inv : {x y : obj G} (f : hom x y) → inv f ∘ f ≡ id
    right-inv : {x y : obj G} (f : hom x y) → f ∘ inv f ≡ id

Groupoid : ∀ i j → Set _
Groupoid i j = Bundle (IsGroupoid i j)

gpd-is-set : ∀ {i j} → Coercion (Groupoid i j) (Set i)
gpd-is-set {i}{j} = coerce-parent

gpd-is-gph : ∀ {i j} → Coercion (Groupoid i j) (Graph i j)
gpd-is-gph {i}{j} = coerce-parent

gpd-is-cat₀ : ∀ {i j} → Coercion (Groupoid i j) (Category₀ i j)
gpd-is-cat₀ {i}{j} = coerce-parent

gpd-is-cat : ∀ {i j} → Coercion (Groupoid i j) (Category i j)
gpd-is-cat {i}{j} = record
  { coerce = λ G → record
    { parent = cat₀ G
    ; struct = IsGroupoid.is-cat (Bundle.struct G) } }

gpd-is-gpd₀ : ∀ {i j} → Coercion (Groupoid i j) (Groupoid₀ i j)
gpd-is-gpd₀ {i}{j} = coerce-parent

gpd-is-gpd : ∀ {i j} → Coercion (Groupoid i j) (Groupoid i j)
gpd-is-gpd {i}{j} = coerce-self _

private
  module gpd-statics {i j k}{Source : Set k}
                     ⦃ c : Coercion Source (Groupoid i j) ⦄ where
    open Coercion c public using () renaming (coerce to gpd)
  module gpd-methods {i j}{G : Groupoid₀ i j}
                     ⦃ s : Styled default (IsGroupoid i j G) ⦄ where
    open Styled s
    open IsGroupoid value public

module as-groupoid {i j k}{Source : Set k}
                   ⦃ c : Coercion Source (Groupoid i j) ⦄
                   (source : Source) where
  private target = coerce c source
  open as-category₀ target public
  _cat-instance = styled default (cat target)
  _gpd-instance = styled default (Bundle.struct target)

mk-groupoid : ∀ {i j} → GroupoidBuilder i j → Groupoid i j
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
