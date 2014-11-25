{-# OPTIONS --without-K #-}
module container.m.from-nat where

open import sum
open import equality
open import function
open import sets.nat
open import sets.unit
open import hott.level

private
  module Limit {i} (X : ℕ → Set i)
                   (π : (n : ℕ) → X (suc n) → X n) where
    L : Set _
    L = Σ ((n : ℕ) → X n) λ x
      → (∀ n → π n (x (suc n)) ≡ x n)

    p : (n : ℕ) → L → X n
    p n (x , q) = x n


    β : (n : ℕ) → ∀ x → π n (p (suc n) x) ≡ p n x
    β n (x , q) = q n

  module Limit-op {i} (X : ℕ → Set i)
                      (ρ : (n : ℕ) → X n → X (suc n)) where
    L : Set _
    L = Σ ((n : ℕ) → X n) λ x
      → (∀ n → ρ n (x n) ≡ x (suc n))

    limit-op-contr : L ≅ X 0
    limit-op-contr = begin
        L
      ≅⟨ ( Σ-ap-iso refl≅ λ x → sym≅ ×-left-unit) ⟩
        ( Σ ((n : ℕ) → X n) λ x
        → Σ ⊤ λ _
        → (∀ n → ρ n (x n) ≡ x (suc n)) )
      ≅⟨ ( Σ-ap-iso refl≅ λ x
          → Σ-ap-iso (sym≅ (contr-⊤-iso (singl-contr' (x zero)))) (λ _ → refl≅)
          ·≅ Σ-assoc-iso ) ·≅ Σ-comm-iso ⟩
        ( Σ (X 0) λ z
        → Σ ((n : ℕ) → X n) λ x
        → Σ (z ≡ x 0) λ _
        → (∀ n → ρ n (x n) ≡ x (suc n)) )
      ≅⟨ (Σ-ap-iso refl≅ λ z → contr-⊤-iso (ℕ-initial X z ρ)) ·≅ ×-right-unit ⟩
        X 0
      ∎
      where
        open ≅-Reasoning
