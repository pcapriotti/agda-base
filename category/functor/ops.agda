{-# OPTIONS --without-K --type-in-type #-}

module category.functor.ops where

open import equality.core
open import function.core
open import function.overloading
open import category.graph.core
open import category.graph.morphism.core
open import category.graph.morphism.ops
open import category.category.core
open import category.category.zero
open import category.functor.core
open import overloading.bundle

private
  Id : (C : Category) → Functor C C
  Id C = bundle id record
    { map-id = λ _ → refl
    ; map-hom = λ _ _ → refl }

  Compose : {C D E : Category} → Functor D E → Functor C D → Functor C E
  Compose {C = C}{D}{E} F G = bundle H record
    { map-id = H-map-id
    ; map-hom = H-map-hom }
    where
      open import equality.calculus using (_⊚_)

      open as-category C
      open as-category D
      open as-category E

      H : Morphism (graph C) (graph E)
      H = Bundle.parent F ∘ Bundle.parent G

      H-map-id : (x : obj C) → map H (id {X = x}) ≡ id
      H-map-id x = cong (map F) (map-id G x) ⊚ map-id F (apply G x)

      H-map-hom : {x y z : obj C}
                  (f : hom y z)
                  (g : hom x y)
                → map H (f ∘ g)
                ≡ map H f ∘ map H g
      H-map-hom f g = cong (map F) (map-hom G f g)
                    ⊚ map-hom F (map G f) (map G g)

Const : (C : Category){D : Category} → obj D → Functor C D
Const C {D} X = mk-functor record
  { apply = λ _ → X
  ; map = λ _ → id
  ; map-id = λ _ → refl
  ; map-hom = λ _ _ → sym (left-id _) }
  where open as-category D

fct-identity : Identity
fct-identity = record
  { U = Category
  ; endo = λ C → Functor C C
  ; id = λ {W} → Id W }

fct-comp : Composition
fct-comp = record
  { U₁ = Category
  ; U₂ = Category
  ; U₃ = Category
  ; hom₁₂ = Functor
  ; hom₂₃ = Functor
  ; hom₁₃ = Functor
  ; _∘_ = Compose }

cat-cat₀ : Category₀
cat-cat₀ = mk-category₀ record
  { obj = Category
  ; hom = Functor
  ; id = Id
  ; _∘_ = Compose }
