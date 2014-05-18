{-# OPTIONS --without-K #-}

module hott.equivalence.properties where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.extensionality
open import hott.equivalence.core
open import hott.equivalence.alternative
open import hott.univalence
open import hott.level

sym≈ : ∀ {i j}{X : Set i}{Y : Set j}
     → X ≈ Y → Y ≈ X
sym≈ = ≅'⇒≈ ∘ sym≅' ∘ ≈⇒≅'

-- being a weak equivalence is propositional
we-h1 : ∀ {i j}{X : Set i}{Y : Set j}
      → (f : X → Y)
      → h 1 (weak-equiv f)
we-h1 f = Π-level λ _ → contr-h1 _

apply≈-inj : ∀ {i j}{X : Set i}{Y : Set j}
           → injective (apply≈ {X = X}{Y = Y})
apply≈-inj {x = (f , w)}{.f , w'} refl =
  unapΣ (refl , h1⇒prop (we-h1 f) w w')

abstract
  univ-sym≈ : ∀ {i}{X Y : Set i}
            → (w : X ≈ Y)
            → sym (≈⇒≡ w)
            ≡ ≈⇒≡ (sym≈ w)
  univ-sym≈ {i}{X}{Y} w = inverse-unique p q lem-inv
    where
      p : X ≡ Y
      p = ≈⇒≡ w

      q : Y ≡ X
      q = ≈⇒≡ (sym≈ w)

      p-β : coerce p ≡ apply≈ w
      p-β = uni-coherence w

      q-β : coerce q ≡ invert≈ w
      q-β = uni-coherence (sym≈ w)

      lem : coerce (p · q) ≡ coerce refl
      lem = coerce-hom p q
          · (ap (λ h → coerce q ∘ h) p-β
          · ap (λ h → h ∘ apply≈ w) q-β
          · funext (_≅_.iso₁ (≈⇒≅ w)))

      lem-inv : p · q ≡ refl
      lem-inv = iso⇒inj uni-iso (apply≈-inj lem)
