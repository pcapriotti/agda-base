{-# OPTIONS --without-K #-}
module category.instances.discrete where

open import sum
open import category.category
  hiding (right-unit)
  renaming (left-unit to cat-left-unit)
open import category.univalence
open import category.groupoid
open import category.functor using (Functor)
open import category.isomorphism
open import equality.core
import equality.properties as E
open import equality.calculus
open import function.isomorphism
open import hott.hlevel
open import hott.weak-equivalence

open Groupoid using (cat)

discrete : ∀ {i} → Type i 1 → Groupoid i i
discrete (A , h3) = record
  { cat = record
    { graph = record
      { obj = A
      ; is-gph = record { hom = _≡_ } }
    ; is-cat = record
      { id = λ x → refl {x = x}
      ; _∘_ = λ p q → trans q p
      ; left-unit = left-unit
      ; right-unit = right-unit
      ; associativity = E.associativity }
    ; trunc = h3 }
  ; is-grpd = record
    { _⁻¹ = sym
    ; left-inverse = left-inverse
    ; right-inverse = right-inverse } }

discrete-cat : ∀ {i} → Type i 1 → Category i i
discrete-cat A = cat (discrete A)

discrete-lift : ∀ {i j k}{A : Type i 1}{C : Category j k}
              → (proj₁ A → obj C)
              → Functor (discrete-cat A) C
discrete-lift {C = C} f = record
  { morph = record
    { apply = f
    ; map = λ { {X}{.X} refl → id _ } }
  ; is-func = record
    { map-id = λ _ → refl
    ; map-hom = λ { {X}{.X}{.X} refl refl
                  → sym (cat-left-unit _) } } }

discrete-func : ∀ {i j}{A : Type i 1}{B : Type j 1}
              → (proj₁ A → proj₁ B)
              → Functor (discrete-cat A) (discrete-cat B)
discrete-func f = discrete-lift f

discrete-univ : ∀ {i} (A : Type i 1) → univalent (discrete-cat A)
discrete-univ A x y = proj₂ (≅⇒≈ lem-iso)
  where
    C = discrete-cat A

    iso₁ : ∀ {x y} → (p : x ≡ y)
         → cat-iso.to (≡⇒iso C p) ≡ p
    iso₁ refl = refl

    iso₁' : ∀ {x y} → (p : x ≡ y)
          → cat-iso.from (≡⇒iso C p) ≡ sym p
    iso₁' refl = refl

    iso-inv : ∀ {x y} → (isom : cat-iso C x y)
            → sym (cat-iso.to isom) ≡ cat-iso.from isom
    iso-inv isom = inverse-unique _ _ (cat-iso.iso₁ isom)

    iso₂ : ∀ {x y} → (isom : cat-iso C x y)
        → ≡⇒iso C (cat-iso.to isom) ≡ isom
    iso₂ isom = cat-iso-equality
      (iso₁ (cat-iso.to isom))
      (iso₁' (cat-iso.to isom) ⊚ iso-inv isom)

    lem-iso : (x ≡ y) ≅ cat-iso C x y
    lem-iso = record
      { to = ≡⇒iso C
      ; from = cat-iso.to
      ; iso₁ = iso₁
      ; iso₂ = iso₂ }
