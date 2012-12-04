{-# OPTIONS --without-K #-}
module category.instances.discrete where

open import category.groupoid
open import category.functor using () renaming (id to Id)
open import equality.core using (_≡_ ; refl ; sym ; trans ; cong)
open import equality.properties
open import function using (id)

open Groupoid using (cat)

discrete : ∀ {i}(A : Set i) → Groupoid i i
discrete A = record
  { cat = record
    { obj = A
    ; hom = _≡_
    ; id = λ x → refl {x = x}
    ; _∘_ = λ p q → trans q p
    ; left-unit = left-unit
    ; right-unit = right-unit
    ; associativity = associativity }
  ; _⁻¹ = sym
  ; left-inverse = left-inverse
  ; right-inverse = right-inverse }
  
module DiscreteGroupoid {i}{X : Set i} = Groupoid (discrete X)

discrete-map : ∀ {i j}{A : Set i}{B : Set j}
             → (A → B)
             → Morphism (discrete A) (discrete B)
discrete-map {A = A} f = record
  { apply = f
  ; map = cong f
  ; map-id = λ _ → refl
  ; map-hom = map-hom }
  where
    open DiscreteGroupoid
    map-hom : {x y z : A} → (p : x ≡ y)(q : y ≡ z)
            → cong f (p ⊚ q) ≡ cong f p ⊚ cong f q
    map-hom refl q = refl