{-# OPTIONS --without-K #-}
module function.isomorphism.properties where

open import level
open import sum
open import sets.nat
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.isomorphism
open import hott.coherence
open import hott.hlevel

private
  module Dummy {i j}{X : Set i}{Y : Set j}
               (isom' : X ≅' Y) where
    private
      isom : X ≅ Y
      isom = proj₁ isom'

      γ : isCoherent isom
      γ = proj₂ isom'

    open _≅_ isom
    open ≡-Reasoning
      
    iso'≡ : {x x' : X} → (x ≡ x') ≅ (to x ≡ to x')
    iso'≡ {x}{x'} = iso u v H K
      where
        u : ∀ {x x'} → x ≡ x' → to x ≡ to x'
        u = cong to

        v : ∀ {x x'} → to x ≡ to x' → x ≡ x'
        v {x}{x'} q = iso₁ x ⁻¹ ⊚ cong from q ⊚ iso₁ x'

        H : ∀ {x x'} (p : x ≡ x') → v (u p) ≡ p
        H {x}{.x} refl =
            cong (λ α → α ⊚ (iso₁ x)) (left-unit (sym (iso₁ x)))
          ⊚ right-inverse (iso₁ x)

        K' : ∀ {x y}(q : to x ≡ y)
          → cong to (iso₁ x ⁻¹ ⊚ cong from q) ≡ q ⊚ iso₂ y ⁻¹
        K' {x} refl = begin
            cong to (iso₁ x ⁻¹ ⊚ refl)
          ≡⟨ cong (cong to) (left-unit (iso₁ x ⁻¹)) ⟩
            cong to (iso₁ x ⁻¹)
          ≡⟨ cong-inv to (iso₁ x) ⟩
            cong to (iso₁ x) ⁻¹
          ≡⟨ cong _⁻¹ (γ x) ⟩
            iso₂ (to x) ⁻¹
          ≡⟨ refl ⟩
            refl ⊚ iso₂ (to x) ⁻¹
          ∎

        K : (q : to x ≡ to x')
          → cong to (iso₁ x ⁻¹ ⊚ cong from q ⊚ iso₁ x') ≡ q
        K q = begin
            cong to (iso₁ x ⁻¹ ⊚ cong from q ⊚ iso₁ x')
          ≡⟨ cong-map-hom to (iso₁ x ⁻¹ ⊚ cong from q) (iso₁ x') ⟩
            cong to (iso₁ x ⁻¹ ⊚ cong from q) ⊚ cong to (iso₁ x')
          ≡⟨ cong₂ _⊚_ (K' q) (γ x') ⟩
            q ⊚ iso₂ (to x') ⁻¹ ⊚ iso₂ (to x')
          ≡⟨ lem q _ ⟩
            q
          ∎
          where
            lem : ∀ {i}{X : Set i} {x y z : X}
                → (p : x ≡ y)
                → (q : z ≡ y)
                → p ⊚ q ⁻¹ ⊚ q ≡ p
            lem refl q = right-inverse q
open Dummy public

iso≡ : ∀ {i j}{X : Set i}{Y : Set j}
     → (isom : X ≅ Y)
     → {x x' : X}
     → (x ≡ x')
     ≅ (apply isom x ≡ apply isom x')
iso≡ isom = iso'≡ (≅⇒≅' isom)

-- isomorphisms preserve h-levels
iso-h : ∀ {i j}{X : Set i}{Y : Set j}
      → X ≅ Y
      → (n : ℕ)
      → h n X
      → h n Y
iso-h {Y = Y} isom 0 (x , f) = to x , f'
  where
    open _≅_ isom

    f' : (y : Y) → to x ≡ y
    f' y = cong to (f (from y)) ⊚ iso₂ y
iso-h {Y = Y} isom (suc n) f = f'
  where
    open _≅_ isom

    f' : (y y' : Y) → h n (y ≡ y')
    f' y y' = subst₂ (λ α β → h n (α ≡ β))
                     (iso₂ y)
                     (iso₂ y')
                     (iso-h (iso≡ isom) n (f (from y) (from y')))

-- lifting is an isomorphism
lift-iso : ∀ {i} j (X : Set i) → X ≅ ↑ j X
lift-iso j X = iso lift lower (λ _ → refl) (λ _ → refl)
