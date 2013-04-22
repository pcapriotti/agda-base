{-# OPTIONS --without-K #-}

module category2.groupoid.core where

open import level
open import function.core
open import equality.core
open import overloading
open import category2.category.zero
open import category2.category.core
open import category2.graph.core
open import category2.groupoid.builder
open import category2.groupoid.zero

record IsGroupoid i j (G : Groupoid₀ i j) : Set (i ⊔ j) where
  open as-groupoid₀ G

  field
    is-cat : IsCategory i j (cat₀ G)
    left-inv : {x y : obj G} (f : hom x y) → inv f ∘ f ≡ id
    right-inv : {x y : obj G} (f : hom x y) → f ∘ inv f ≡ id

Groupoid : ∀ i j → Set _
Groupoid i j = Bundle (IsGroupoid i j)

gpd-is-set : ∀ {i j} → Overload _ (Set i)
gpd-is-set {i}{j} = overload-parent (IsGroupoid i j)

gpd-is-gph : ∀ {i j} → Overload _ (Graph i j)
gpd-is-gph {i}{j} = overload-parent (IsGroupoid i j)

gpd-is-cat₀ : ∀ {i j} → Overload _ (Category₀ i j)
gpd-is-cat₀ {i}{j} = overload-parent (IsGroupoid i j)

gpd-is-cat : ∀ {i j} → Overload _ (Category i j)
gpd-is-cat {i}{j} = record
  { Source = Groupoid i j
  ; coerce = λ G → record
    { parent = cat₀ G
    ; struct = IsGroupoid.is-cat (Bundle.struct G) } }

gpd-is-gpd₀ : ∀ {i j} → Overload _ (Groupoid₀ i j)
gpd-is-gpd₀ {i}{j} = overload-parent (IsGroupoid i j)

gpd-is-gpd : ∀ {i j} → Overload _ (Groupoid i j)
gpd-is-gpd {i}{j} = overload-self (Groupoid i j)

private
  module gpd-statics {i j k} ⦃ o : Overload k (Groupoid i j) ⦄ where
    open Overload o public using () renaming (coerce to gpd)
  module gpd-methods {i j k} ⦃ o : OverloadInstance k default (Groupoid i j) ⦄ where
    open OverloadInstance o
    open IsGroupoid (Bundle.struct target) public

module as-groupoid {i j k} ⦃ o : Overload k (Groupoid i j) ⦄
                    (source : Source o) where
  private target = coerce o source

  open as-category₀ target public
    renaming (_instance to _parent-instance)
  open overload default (Category i j) target public
    renaming (_instance to _cat-instance)
  open overload default (Groupoid i j) target public

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
