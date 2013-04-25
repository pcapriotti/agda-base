{-# OPTIONS --without-K #-}

module category.groupoid.zero where

open import level

open import overloading
open import category.category.zero
open import category.graph.core
open import category.groupoid.builder

record IsGroupoid₀ i j (C : Category₀ i j) : Set (i ⊔ j) where
  open as-category₀ C

  field
    inv : {x y : obj C} → hom x y → hom y x

Groupoid₀ : ∀ i j → Set _
Groupoid₀ i j = Bundle (IsGroupoid₀ i j)

gpd₀-is-set : ∀ {i j} → Overload _ (Set i)
gpd₀-is-set {i}{j} = overload-parent (IsGroupoid₀ i j)

gpd₀-is-gph : ∀ {i j} → Overload _ (Graph i j)
gpd₀-is-gph {i}{j} = overload-parent (IsGroupoid₀ i j)

gpd₀-is-cat₀ : ∀ {i j} → Overload _ (Category₀ i j)
gpd₀-is-cat₀ {i}{j} = overload-parent (IsGroupoid₀ i j)

gpd₀-is-gpd₀ : ∀ {i j} → Overload _ (Groupoid₀ i j)
gpd₀-is-gpd₀ {i}{j} = overload-self (Groupoid₀ i j)

private
  module gpd₀-statics {i j k} ⦃ o : Overload k (Groupoid₀ i j) ⦄ where
    open Overload o public using () renaming (coerce to gpd₀)
  module gpd₀-methods {i j k} ⦃ o : OverloadInstance k default (Groupoid₀ i j) ⦄ where
    open OverloadInstance o
    open IsGroupoid₀ (Bundle.struct target) public

module as-groupoid₀ {i j k} ⦃ o : Overload k (Groupoid₀ i j) ⦄
                    (source : Source o) where
  private target = coerce o source

  open as-category₀ target public
    renaming (_instance to _parent-instance)
  open overload default (Groupoid₀ i j) target public

mk-groupoid₀ : ∀ {i j} → Groupoid₀Builder i j → Groupoid₀ i j
mk-groupoid₀ b = let module B = Groupoid₀Builder b in record
  { parent = mk-category₀ record
    { obj = B.obj
    ; hom = B.hom
    ; id = B.id
    ; _∘_ = B._∘_ }
  ; struct = record
    { inv = B.inv } }

open gpd₀-statics public
open gpd₀-methods public
