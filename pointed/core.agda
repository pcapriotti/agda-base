{-# OPTIONS --without-K #-}
module pointed.core where

open import sum
open import equality.core
open import function.core
open import function.isomorphism.core

PSet : ∀ i → Set _
PSet i = Σ (Set i) λ X → X

PMap : ∀ {i j} → PSet i → PSet j → Set _
PMap (X , x) (Y , y) = Σ (X → Y) λ f → f x ≡ y

_∘P_ : ∀ {i j k}{𝓧 : PSet i}{𝓨 : PSet j}{𝓩 : PSet k}
     → PMap 𝓨 𝓩 → PMap 𝓧 𝓨 → PMap 𝓧 𝓩
(g , q) ∘P (f , p) = (g ∘ f , ap g p · q)

instance
  pmap-comp : ∀ {i j k} → Composition _ _ _ _ _ _
  pmap-comp {i}{j}{k} = record
    { U₁ = PSet i
    ; U₂ = PSet j
    ; U₃ = PSet k
    ; hom₁₂ = PMap
    ; hom₂₃ = PMap
    ; hom₁₃ = PMap
    ; _∘_ = _∘P_ }
