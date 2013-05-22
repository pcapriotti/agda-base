{-# OPTIONS --without-K --type-in-type #-}

module category.category.zero where

open import overloading.core
open import overloading.bundle
open import category.graph.core
open import category.category.builder

record IsCategory₀ (W : Graph) : Set where
  open as-graph W

  field
    id : (x : obj W) → hom x x
    _∘_ : {x y z : obj W} → hom y z → hom x y → hom x z

Category₀ : Set
Category₀ = Bundle IsCategory₀

cat₀-is-set : Coercion Category₀ Set
cat₀-is-set = coerce-parent

cat₀-is-gph : Coercion Category₀ Graph
cat₀-is-gph = coerce-parent

cat₀-is-cat₀ : Coercion Category₀ Category₀
cat₀-is-cat₀ = coerce-self _

private
  module cat₀-statics {Source : Set}
                      ⦃ c : Coercion Source Category₀ ⦄ where
    open Coercion c public using () renaming (coerce to cat₀)
  module cat₀-methods {W : Graph}
                      ⦃ s : Styled default (IsCategory₀ W) ⦄ where
    open Styled s
    open IsCategory₀ value public
      hiding (_∘_; id)

module as-category₀  {Source : Set}
                    ⦃ o : Coercion Source Category₀ ⦄
                    (source : Source) where
  open import function.core
  private target = coerce o source

  open as-graph target public
  _cat₀-instance = styled default (Bundle.struct target)

  cat-comp : Composition
  cat-comp = record
    { U₁ = obj target
    ; U₂ = obj target
    ; U₃ = obj target
    ; hom₁₂ = λ x y → hom x y
    ; hom₂₃ = λ x y → hom x y
    ; hom₁₃ = λ x y → hom x y
    ; _∘_ = λ f g → IsCategory₀._∘_ (Bundle.struct target) f g }

  cat-identity : Identity
  cat-identity = record
    { U = obj target
    ; endo = λ x → hom x x
    ; id = λ {x} → IsCategory₀.id (Bundle.struct target) x }

mk-category₀ : Category₀Builder → Category₀
mk-category₀ b = let module B = Category₀Builder b in record
  { parent = mk-graph record
    { obj = B.obj
    ; hom = B.hom }
  ; struct = record
    { id = B.id
    ; _∘_ = B._∘_ } }

open cat₀-statics public
open cat₀-methods public
