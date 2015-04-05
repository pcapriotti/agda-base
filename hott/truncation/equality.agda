{-# OPTIONS --without-K #-}
module hott.truncation.equality where

open import sum
open import equality
open import function.isomorphism
open import function.overloading
open import sets.nat
open import hott.level.core
open import hott.truncation.core

private

  J-extend : ∀ {i j}{X : Set i}{Y : X → X → Set j}
           → ((x : X) → Y x x)
           → ({x y : X} → x ≡ y → Y x y)
  J-extend f refl = f _

  module _ {i}{X : Set i}(n-1 : ℕ) where
    n : ℕ
    n = suc n-1

    Trunc-dep-iso₂ : ∀ {j} (Z : Trunc n X → Trunc n X → Set j)
                   → ((c c' : Trunc n X) → h n (Z c c'))
                   → ((c c' : Trunc n X) → Z c c')
                   ≅ ((x y : X) → Z [ x ] [ y ])
    Trunc-dep-iso₂ Z hZ = begin
        ((c c' : Trunc n X) → Z c c')
      ≅⟨ (Π-ap-iso refl≅ λ c → Trunc-dep-iso n (Z c) (hZ c)) ⟩
        ((c : Trunc n X)(y : X) → Z c [ y ])
      ≅⟨ Trunc-dep-iso n (λ c → (y : X) → Z c [ y ]) {!!} ⟩
        ((x y : X) → Z [ x ] [ y ])
      ∎
      where open ≅-Reasoning

    trunc-eq-iso : ( Σ (Trunc n X → Trunc n X → Type i (n-1)) λ P
                   → Σ ((c : Trunc n X) → proj₁ (P c c)) λ r
                   → Σ ((c c' : Trunc n X) → proj₁ (P c c') → c ≡ c') λ f
                   → ((c : Trunc n X) → f c c (r c) ≡ refl) )
                 ≅ ( Σ (X → X → Type i (n-1)) λ P
                   → Σ ((x : X) → proj₁ (P x x)) λ r
                   → Σ ((x y : X) → proj₁ (P x y) → _≡_ {A = Trunc n X} [ x ] [ y ]) λ f
                   → ((x : X) → f x x (r x) ≡ refl) )
    trunc-eq-iso = Σ-ap-iso (Trunc-dep-iso₂ (λ _ _ → Type i (n-1)) {!!}) λ P
                 → Σ-ap-iso (Trunc-dep-iso n (λ c → proj₁ (P c c)) {!!}) λ r
                 → Σ-ap-iso (Trunc-dep-iso₂ (λ c c' → proj₁ (P c c') → c ≡ c') {!!}) λ f
                 → Trunc-dep-iso n (λ c → f c c (r c) ≡ refl) {!!}

    P₀ : X → X → Type _ (n-1)
    P₀ x y = Trunc (n-1) (x ≡ y) , Trunc-level n-1

    r₀ : (x : X) → proj₁ (P₀ x x)
    r₀ x = [ refl ]

    trunc-eq-iso₂ : ( Σ ((x y : X) → proj₁ (P₀ x y) → _≡_ {A = Trunc n X} [ x ] [ y ]) λ f
                    → ((x : X) → f x x [ refl ] ≡ refl) )
                  ≅ ( Σ ((x y : X) → x ≡ y → _≡_ {A = Trunc n X} [ x ] [ y ]) λ f
                    → ((x : X) → f x x refl ≡ refl) )
    trunc-eq-iso₂ = Σ-ap-iso ( Π-ap-iso refl≅ λ x
                             → Π-ap-iso refl≅ λ y
                             → Trunc-elim-iso n-1 (x ≡ y) _ {!!}) λ f
                  → Π-ap-iso refl≅ λ x → refl≅

    f₁ : (x y : X) → x ≡ y → _≡_ {A = Trunc n X} [ x ] [ y ]
    f₁ x .x refl = refl

    ρ₁ : (x : X) → f₁ x x refl ≡ refl
    ρ₁ x = refl

    trunc-eq-data₂ = invert trunc-eq-iso₂ (f₁ , ρ₁)

    f₀ : (x y : X) → proj₁ (P₀ x y) → _≡_ {A = Trunc n X} [ x ] [ y ]
    f₀ = proj₁ trunc-eq-data₂

    ρ₀ : (x : X) → f₀ x x [ refl ] ≡ refl
    ρ₀ = proj₂ trunc-eq-data₂

    trunc-eq-data : Σ (Trunc n X → Trunc n X → Type i (n-1)) λ P
                  → Σ ((c : Trunc n X) → proj₁ (P c c)) λ r
                  → Σ ((c c' : Trunc n X) → proj₁ (P c c') → c ≡ c') λ f
                  → ((c : Trunc n X) → f c c (r c) ≡ refl)
    trunc-eq-data = invert trunc-eq-iso (P₀ , r₀ , f₀ , ρ₀)

    P : Trunc n X → Trunc n X → Type i (n-1)
    P = proj₁ trunc-eq-data

    r : (c : Trunc n X) → proj₁ (P c c)
    r = proj₁ (proj₂ trunc-eq-data)

    f : {c c' : Trunc n X} → proj₁ (P c c') → c ≡ c'
    f = proj₁ (proj₂ (proj₂ trunc-eq-data)) _ _

    ρ : (c : Trunc n X) → f (r c) ≡ refl
    ρ = proj₂ (proj₂ (proj₂ trunc-eq-data))

    g : {c c' : Trunc n X} → c ≡ c' → proj₁ (P c c')
    g {c} refl = r c

    β : (c c' : Trunc n X)(p : c ≡ c') → f (g p) ≡ p
    β c .c refl = ρ c

    α : (c c' : Trunc n X)(u : proj₁ (P c c')) → g (f u) ≡ u
    α = {!!}
