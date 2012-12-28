{-# OPTIONS --without-K #-}
module category.instances.discrete where

open import sum
open import category.category
open import category.groupoid
open import category.functor using (Functor)
open import equality.core
import equality.properties as E
open import equality.calculus
open import hott.hlevel

open Groupoid using (cat)
open Category using (obj; id)
  renaming (left-unit to cat-left-unit)

discrete : ∀ {i} → Type i 1 → Groupoid i i
discrete (A , h3) = record
  { cat = record
    { obj = A
    ; hom = _≡_
    ; trunc = h3
    ; id = λ x → refl {x = x}
    ; _∘_ = λ p q → trans q p
    ; left-unit = left-unit
    ; right-unit = right-unit
    ; associativity = E.associativity }
  ; _⁻¹ = sym
  ; left-inverse = left-inverse
  ; right-inverse = right-inverse }

discrete-cat : ∀ {i} → Type i 1 → Category i i
discrete-cat A = cat (discrete A)

discrete-lift : ∀ {i j k}{A : Type i 1}{C : Category j k}
              → (proj₁ A → obj C)
              → Functor (discrete-cat A) C
discrete-lift {C = C} f = record
  { apply = f
  ; map = λ { {X}{.X} refl → id C _ }
  ; map-id = λ _ → refl
  ; map-hom = λ { {X}{.X}{.X} refl refl
                → sym (cat-left-unit C _) } }

discrete-func : ∀ {i j}{A : Type i 1}{B : Type j 1}
              → (proj₁ A → proj₁ B)
              → Functor (discrete-cat A) (discrete-cat B)
discrete-func f = discrete-lift f
