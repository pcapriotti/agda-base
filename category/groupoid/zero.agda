{-# OPTIONS --type-in-type --without-K #-}

module category.groupoid.zero where

open import overloading
open import category.category.zero
open import category.graph.core
open import category.groupoid.builder

record IsGroupoid₀ (C : Category₀) : Set where
  open as-category₀ C

  field
    inv : {x y : obj C} → hom x y → hom y x

Groupoid₀ : Set
Groupoid₀ = Bundle IsGroupoid₀

gpd₀-is-set : Coercion Groupoid₀ Set
gpd₀-is-set = coerce-parent

gpd₀-is-gph : Coercion Groupoid₀ Graph
gpd₀-is-gph = coerce-parent

gpd₀-is-cat₀ : Coercion Groupoid₀ Category₀
gpd₀-is-cat₀ = coerce-parent

gpd₀-is-gpd₀ : Coercion Groupoid₀ Groupoid₀
gpd₀-is-gpd₀ = coerce-self _

private
  module gpd₀-statics {Source : Set} ⦃ c : Coercion Source Groupoid₀ ⦄ where
    open Coercion c public using () renaming (coerce to gpd₀)
  module gpd₀-methods {C : Category₀} ⦃ s : Styled default (IsGroupoid₀ C) ⦄ where
    open Styled s
    open IsGroupoid₀ value public

module as-groupoid₀ {Source : Set} ⦃ c : Coercion Source Groupoid₀ ⦄
                    (source : Source) where
  private target = coerce c source

  open as-category₀ target public
  _gpd₀-instance = styled default (Bundle.struct target)

mk-groupoid₀ : Groupoid₀Builder → Groupoid₀
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
