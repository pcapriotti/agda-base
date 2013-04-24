{-# OPTIONS --without-K #-}
module category2.instances.discrete where

open import sum
open import category2.category
open import category2.graph
open import category2.univalence
open import category2.groupoid
open import category2.functor
open import category2.isomorphism
open import equality.core
import equality.properties as E
open import equality.calculus
open import function.core
open import function.isomorphism
open import hott.hlevel
open import hott.weak-equivalence
open import overloading.core

discrete₀ : ∀ {i} → Set i → Groupoid₀ i i
discrete₀ X = mk-groupoid₀ record
  { obj = X
  ; hom = _≡_
  ; id = λ _ → refl
  ; _∘_ = λ p q → q ⊚ p
  ; inv = sym }

discrete : ∀ {i} → Type i 1 → Groupoid i i
discrete (X , hX) = mk-groupoid record
  { obj = X
  ; hom = _≡_
  ; id = λ _ → refl
  ; _∘_ = λ p q → q ⊚ p
  ; inv = sym
  ; trunc = hX
  ; left-id = left-unit
  ; right-id = right-unit
  ; assoc = λ p q r → E.associativity r q p
  ; left-inv = left-inverse
  ; right-inv = right-inverse }

discrete-cat : ∀ {i} → Type i 1 → Category i i
discrete-cat A = cat (discrete A)

discrete-lift : ∀ {i j k}{A : Type i 1}{C : Category j k}
              → (proj₁ A → obj C)
              → Functor (discrete-cat A) C
discrete-lift {A = A}{C = C} f = mk-functor record
  { apply = f
  ; map = d-map
  ; map-id = λ x → refl
  ; map-hom = d-map-hom }
  where
    open as-category C

    d-map : {x y : proj₁ A} → x ≡ y → hom (f x) (f y)
    d-map refl = id

    d-map-hom : {x y z : proj₁ A}
                (q : y ≡ z)(p : x ≡ y)
              → d-map (p ⊚ q)
              ≡ d-map q ∘ d-map p
    d-map-hom refl refl = sym (left-id _)

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
