{-# OPTIONS --without-K #-}

module category.functor.ops where

open import equality.core
open import function.core
open import function.overloading
open import category.graph
open import category.category
open import category.functor.core
open import overloading.bundle

private
  Id : ∀ {i j} (C : Category i j) → Functor C C
  Id C = bundle id record
    { map-id = λ _ → refl
    ; map-hom = λ _ _ → refl }

  Compose : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
            {C : Category i₁ j₁}
            {D : Category i₂ j₂}
            {E : Category i₃ j₃}
          → Functor D E
          → Functor C D
          → Functor C E
  Compose {C = C}{D}{E} F G = bundle H record
    { map-id = H-map-id
    ; map-hom = H-map-hom }
    where
      open import equality.calculus using (_·_)

      open as-category C
      open as-category D
      open as-category E

      H : Morphism (graph C) (graph E)
      H = Bundle.parent F ∘ Bundle.parent G

      H-map-id : (x : obj C) → map H (id {X = x}) ≡ id
      H-map-id x = ap (map F) (map-id G x) · map-id F (apply G x)

      H-map-hom : {x y z : obj C}
                  (f : hom y z)
                  (g : hom x y)
                → map H (f ∘ g)
                ≡ map H f ∘ map H g
      H-map-hom f g = ap (map F) (map-hom G f g)
                    · map-hom F (map G f) (map G g)

Const : ∀ {i₁ j₁ i₂ j₂}(C : Category i₁ j₁){D : Category i₂ j₂}
      → obj D → Functor C D
Const C {D} X = mk-functor record
  { apply = λ _ → X
  ; map = λ _ → id
  ; map-id = λ _ → refl
  ; map-hom = λ _ _ → sym (left-id _) }
  where open as-category D

fct-identity : ∀ {i j} → Identity _ _
fct-identity {i}{j} = record
  { U = Category i j
  ; endo = λ C → Functor C C
  ; id = λ {W} → Id W }

fct-comp : ∀ {i₁ j₁ i₂ j₂ i₃ j₃} → Composition _ _ _ _ _ _
fct-comp {i₁}{j₁}{i₂}{j₂}{i₃}{j₃} = record
  { U₁ = Category i₁ j₁
  ; U₂ = Category i₂ j₂
  ; U₃ = Category i₃ j₃
  ; hom₁₂ = Functor
  ; hom₂₃ = Functor
  ; hom₁₃ = Functor
  ; _∘_ = Compose }

cat-cat₀ : ∀ {i j} → Category₀ _ _
cat-cat₀ {i}{j} = mk-category₀ record
  { obj = Category i j
  ; hom = Functor
  ; id = Id
  ; _∘_ = Compose }
