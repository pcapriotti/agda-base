{-# OPTIONS --without-K #-}
open import container.core

module container.m.coalgebra {li la lb}
  (c : Container li la lb) where

open import sum
open import equality
open import hott.level

open Container c

Coalg : ∀ ℓ → Set _
Coalg ℓ = Σ (I → Set ℓ) λ X → X →ⁱ F X

carrier : ∀ {ℓ} → Coalg ℓ → I → Set ℓ
carrier (X , _) = X

IsMor : ∀ {ℓ₁ ℓ₂}(𝓧 : Coalg ℓ₁)(𝓨 : Coalg ℓ₂)
      → (carrier 𝓧 →ⁱ carrier 𝓨) → Set _
IsMor (X , θ) (Y , ψ) f = ψ ∘ⁱ f ≡ imap f ∘ⁱ θ

Mor : ∀ {ℓ₁ ℓ₂} → Coalg ℓ₁ → Coalg ℓ₂ → Set _
Mor 𝓧 𝓨 = Σ (carrier 𝓧 →ⁱ carrier 𝓨) (IsMor 𝓧 𝓨)
