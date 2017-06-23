{-# OPTIONS --without-K #-}
module pointed.equality where

open import sum
open import equality.core
open import function.extensionality
open import function.isomorphism.core
open import function.isomorphism.utils
open import pointed.core

pmap-eq : ∀ {i j}{X : Set i}{Y : Set j}{x₀ : X}{y₀ : Y}
        → {f : X → Y}{p : f x₀ ≡ y₀}
        → {g : X → Y}{q : g x₀ ≡ y₀}
        → (Σ ((x : X) → f x ≡ g x) λ γ → p ≡ γ x₀ · q)
        ≅ _≡_ {A = PMap (X , x₀) (Y , y₀)} (f , p) (g , q)
pmap-eq {X = X}{Y}{x₀}{y₀} = Σ-ap-iso' strong-funext-iso lem ·≅ Σ-split-iso
  where
    lem : {f : X → Y}{p : f x₀ ≡ y₀}
        → {g : X → Y}{q : g x₀ ≡ y₀}
        → (h : f ≡ g)
        → (p ≡ funext-inv h x₀ · q)
        ≅ (subst (λ u → u x₀ ≡ y₀) h p ≡ q)
    lem refl = refl≅
