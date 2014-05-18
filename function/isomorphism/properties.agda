{-# OPTIONS --without-K #-}
module function.isomorphism.properties where

open import level
open import sum
open import sets.nat.core
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.overloading
open import function.isomorphism.core
open import function.isomorphism.coherent
open import hott.level.core

private
  module Dummy {i j}{X : Set i}{Y : Set j}
               (isom' : X ≅' Y) where
    private
      isom : X ≅ Y
      isom = proj₁ isom'

      γ : coherent isom
      γ = proj₂ isom'

    open _≅_ isom
    open ≡-Reasoning

    iso'≡ : {x x' : X} → (x ≡ x') ≅ (to x ≡ to x')
    iso'≡ {x}{x'} = iso u v H K
      where
        u : ∀ {x x'} → x ≡ x' → to x ≡ to x'
        u = ap to

        v : ∀ {x x'} → to x ≡ to x' → x ≡ x'
        v {x}{x'} q = iso₁ x ⁻¹ · ap from q · iso₁ x'

        H : ∀ {x x'} (p : x ≡ x') → v (u p) ≡ p
        H {x}{.x} refl =
            ap (λ α → α · (iso₁ x)) (left-unit (sym (iso₁ x)))
          · right-inverse (iso₁ x)

        K' : ∀ {x y}(q : to x ≡ y)
          → ap to (iso₁ x ⁻¹ · ap from q) ≡ q · iso₂ y ⁻¹
        K' {x} refl = begin
            ap to (iso₁ x ⁻¹ · refl)
          ≡⟨ ap (ap to) (left-unit (iso₁ x ⁻¹)) ⟩
            ap to (iso₁ x ⁻¹)
          ≡⟨ ap-inv to (iso₁ x) ⟩
            ap to (iso₁ x) ⁻¹
          ≡⟨ ap _⁻¹ (γ x) ⟩
            iso₂ (to x) ⁻¹
          ≡⟨ refl ⟩
            refl · iso₂ (to x) ⁻¹
          ∎

        K : (q : to x ≡ to x')
          → ap to (iso₁ x ⁻¹ · ap from q · iso₁ x') ≡ q
        K q = begin
            ap to (iso₁ x ⁻¹ · ap from q · iso₁ x')
          ≡⟨ ap-map-hom to (iso₁ x ⁻¹ · ap from q) (iso₁ x') ⟩
            ap to (iso₁ x ⁻¹ · ap from q) · ap to (iso₁ x')
          ≡⟨ ap₂ _·_ (K' q) (γ x') ⟩
            q · iso₂ (to x') ⁻¹ · iso₂ (to x')
          ≡⟨ lem q _ ⟩
            q
          ∎
          where
            lem : ∀ {i}{X : Set i} {x y z : X}
                → (p : x ≡ y)
                → (q : z ≡ y)
                → p · q ⁻¹ · q ≡ p
            lem refl q = right-inverse q
open Dummy public

iso≡ : ∀ {i j}{X : Set i}{Y : Set j}
     → (isom : X ≅ Y)
     → {x x' : X}
     → (x ≡ x')
     ≅ (apply isom x ≡ apply isom x')
iso≡ isom = iso'≡ (≅⇒≅' isom)

-- lifting is an isomorphism
lift-iso : ∀ {i} j (X : Set i) → X ≅ ↑ j X
lift-iso j X = iso lift lower (λ _ → refl) (λ _ → refl)

abstract
  subtype-eq : ∀ {i j k}{A : Set i}{P : A → Set j}
             → ((x : A) → h 1 (P x))
             → {X : Set k}
             → (isom : X ≅ Σ A P)
             → {x y : X}
             → (proj₁ (apply isom x) ≡ proj₁ (apply isom y))
             → x ≡ y
  subtype-eq hP isom p = iso⇒inj isom
    (unapΣ (p , h1⇒prop (hP _) _ _))
