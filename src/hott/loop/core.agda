{-# OPTIONS --without-K #-}
module hott.loop.core where

open import sum
open import equality
open import function.core
open import function.isomorphism.core
open import function.overloading
open import pointed.core
open import sets.nat.core

Ω₁ : ∀ {i} → PSet i → PSet i
Ω₁ (X , x) = ((x ≡ x) , refl)

ΩP : ∀ {i} → ℕ → PSet i → PSet _
ΩP 0 𝓧 = 𝓧
ΩP (suc n) 𝓧 = ΩP n (Ω₁ 𝓧)

Ω : ∀ {i} → ℕ → {X : Set i} → X → Set i
Ω n {X} x = proj₁ (ΩP n (X , x))

refl' : ∀ {i} n {X : Set i}(x : X) → Ω n x
refl' n {X} x = proj₂ (ΩP n (X , x))

mapΩ₁ : ∀ {i j} → {𝓧 : PSet i}{𝓨 : PSet j}
     → PMap 𝓧 𝓨 → PMap (Ω₁ 𝓧) (Ω₁ 𝓨)
mapΩ₁ (f , refl) = ap f , refl

mapΩP : ∀ {i j} n → {𝓧 : PSet i}{𝓨 : PSet j}
      → PMap 𝓧 𝓨 → PMap (ΩP n 𝓧) (ΩP n 𝓨)
mapΩP zero f = f
mapΩP (suc n) f = mapΩP n (mapΩ₁ f)

mapΩ : ∀ {i j} n → {X : Set i}{Y : Set j}(f : X → Y)
     → {x : X} → Ω n x → Ω n (f x)
mapΩ n f = proj₁ (mapΩP n (f , refl))

constP : ∀ {i j} (𝓧 : PSet i)(𝓨 : PSet j) → PMap 𝓧 𝓨
constP _ (Y , y) = (λ _ → y) , refl

