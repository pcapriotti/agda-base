{-# OPTIONS --without-K #-}

module category.category.zero where

open import level

open import overloading

open import category.graph.core
open import category.category.builder

record IsCategory₀ i j (W : Graph i j) : Set (i ⊔ j) where
  open as-graph W

  field
    id : (x : obj W) → hom x x
    _∘_ : {x y z : obj W} → hom y z → hom x y → hom x z

Category₀ : ∀ i j → Set _
Category₀ i j = Bundle (IsCategory₀ i j)

cat₀-is-set : ∀ {i j} → Coercion (Category₀ i j) (Set i)
cat₀-is-set {i}{j} = coerce-parent

cat₀-is-gph : ∀ {i j} → Coercion (Category₀ i j) (Graph i j)
cat₀-is-gph {i}{j} = coerce-parent

cat₀-is-cat₀ : ∀ {i j} → Coercion (Category₀ i j) (Category₀ i j)
cat₀-is-cat₀ {i}{j} = coerce-self _

private
  module cat₀-statics {i j k}{Source : Set k}
                      ⦃ c : Coercion Source (Category₀ i j) ⦄ where
    open Coercion c public using () renaming (coerce to cat₀)
  module cat₀-methods {i j}{W : Graph i j}
                      ⦃ s : Styled default (IsCategory₀ i j W) ⦄ where
    open Styled s
    open IsCategory₀ value public
      hiding (_∘_; id)

module as-category₀ {i j k} {Source : Set k}
                    ⦃ o : Coercion Source (Category₀ i j) ⦄
                    (source : Source) where
  open import function.core
  private target = coerce o source

  open as-graph target public
  _cat₀-instance = styled default (Bundle.struct target)

  cat-comp : Composition _ _ _ _ _ _
  cat-comp = record
    { U₁ = obj target
    ; U₂ = obj target
    ; U₃ = obj target
    ; hom₁₂ = λ x y → hom x y
    ; hom₂₃ = λ x y → hom x y
    ; hom₁₃ = λ x y → hom x y
    ; _∘_ = λ f g → IsCategory₀._∘_ (Bundle.struct target) f g }

  cat-identity : Identity _ _
  cat-identity = record
    { U = obj target
    ; endo = λ x → hom x x
    ; id = λ {x} → IsCategory₀.id (Bundle.struct target) x }

mk-category₀ : ∀ {i j} → Category₀Builder i j → Category₀ i j
mk-category₀ b = let module B = Category₀Builder b in record
  { parent = mk-graph record
    { obj = B.obj
    ; hom = B.hom }
  ; struct = record
    { id = B.id
    ; _∘_ = B._∘_ } }

open cat₀-statics public
open cat₀-methods public
