{-# OPTIONS --without-K #-}
module hott.loop.properties where

open import sum
open import equality
open import function.core
open import function.extensionality
open import function.isomorphism.core
open import function.overloading
open import pointed
open import sets.nat.core
open import hott.loop.core

mapΩ₁-const : ∀ {i j}{𝓧 : PSet i}{𝓨 : PSet j}
            → mapΩ₁ (constP 𝓧 𝓨) ≡ constP _ _
mapΩ₁-const = apply pmap-eq (ap-const _ , refl)
  where
    ap-const : ∀ {i j}{X : Set i}{Y : Set j}(y : Y)
             → {x x' : X}(p : x ≡ x') → ap (λ _ → y) p ≡ refl
    ap-const y refl = refl

mapΩP-const : ∀ {i j} n → {𝓧 : PSet i}{𝓨 : PSet j}
            → mapΩP n (constP 𝓧 𝓨) ≡ constP _ _
mapΩP-const zero = refl
mapΩP-const (suc n) = ap (mapΩP n) mapΩ₁-const · mapΩP-const n

mapΩ-const : ∀ {i j} n → {X : Set i}{Y : Set j}(y : Y)
           → (x : X) (p : Ω n x)
           → mapΩ n (λ _ → y) p ≡ refl' n y
mapΩ-const n y x p = funext-inv (ap proj₁ (mapΩP-const n)) p

mapΩ₁-hom : ∀ {i j k}{𝓧 : PSet i}{𝓨 : PSet j}{𝓩 : PSet k}
          → (f : PMap 𝓧 𝓨)(g : PMap 𝓨 𝓩)
          → mapΩ₁ g ∘ mapΩ₁ f ≡ mapΩ₁ (g ∘ f)
mapΩ₁-hom (f , refl) (g , refl) = apply pmap-eq (ap-hom f g , refl)

mapΩP-hom : ∀ {i j k} n → {𝓧 : PSet i}{𝓨 : PSet j}{𝓩 : PSet k}
          → (f : PMap 𝓧 𝓨)(g : PMap 𝓨 𝓩)
          → mapΩP n g ∘ mapΩP n f ≡ mapΩP n (g ∘ f)
mapΩP-hom zero f g = refl
mapΩP-hom (suc n) f g = mapΩP-hom n (mapΩ₁ f) (mapΩ₁ g)
                      · ap (mapΩP n) (mapΩ₁-hom f g)

mapΩ-hom : ∀ {i j k} n {X : Set i}{Y : Set j}{Z : Set k}
         → (f : X → Y)(g : Y → Z){x : X}(p : Ω n x)
         → mapΩ n g (mapΩ n f p) ≡ mapΩ n (g ∘ f) p
mapΩ-hom n f g = proj₁ (invert pmap-eq (mapΩP-hom n (f , refl) (g , refl)))

mapΩ-refl : ∀ {i j} n {X : Set i}{Y : Set j}
          → (f : X → Y){x : X}
          → mapΩ n f (refl' n x) ≡ refl' n (f x)
mapΩ-refl n f = proj₂ (mapΩP n (f , refl))
