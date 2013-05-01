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

gpd₀-is-set : ∀ {i j} → Coercion (Groupoid₀ i j) (Set i)
gpd₀-is-set {i}{j} = coerce-parent

gpd₀-is-gph : ∀ {i j} → Coercion (Groupoid₀ i j) (Graph i j)
gpd₀-is-gph {i}{j} = coerce-parent

gpd₀-is-cat₀ : ∀ {i j} → Coercion (Groupoid₀ i j) (Category₀ i j)
gpd₀-is-cat₀ {i}{j} = coerce-parent

gpd₀-is-gpd₀ : ∀ {i j} → Coercion (Groupoid₀ i j) (Groupoid₀ i j)
gpd₀-is-gpd₀ {i}{j} = coerce-self _

private
  module gpd₀-statics {i j k}{Source : Set k}
                      ⦃ c : Coercion Source (Groupoid₀ i j) ⦄ where
    open Coercion c public using () renaming (coerce to gpd₀)
  module gpd₀-methods {i j}{C : Category₀ i j}
                      ⦃ s : Styled default (IsGroupoid₀ i j C) ⦄ where
    open Styled s
    open IsGroupoid₀ value public

module as-groupoid₀ {i j k} {Source : Set k}
                    ⦃ c : Coercion Source (Groupoid₀ i j) ⦄
                    (source : Source) where
  private target = coerce c source

  open as-category₀ target public
  _gpd₀-instance = styled default (Bundle.struct target)

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
