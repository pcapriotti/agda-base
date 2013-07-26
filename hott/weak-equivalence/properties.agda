{-# OPTIONS --type-in-type --without-K #-}

module hott.weak-equivalence.properties where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.extensionality
open import hott.weak-equivalence.core
open import hott.weak-equivalence.alternative
open import hott.univalence
open import hott.hlevel

sym≈ : {X Y : Set} → X ≈ Y → Y ≈ X
sym≈ = ≅'⇒≈ ∘ sym≅' ∘ ≈⇒≅'

-- being a weak equivalence is propositional
we-h1 : {X Y : Set} → (f : X → Y) → h 1 (weak-equiv f)
we-h1 f = Π-hlevel λ _ → contr-h1 _

apply≈-inj : {X Y : Set} → injective (apply≈ {X = X}{Y = Y})
apply≈-inj {x = (f , w)}{.f , w'} refl =
  uncongΣ (refl , h1⇒prop (we-h1 f) w w')

abstract
  univ-sym≈ : {X Y : Set}
            → (w : X ≈ Y)
            → sym (≈⇒≡ w)
            ≡ ≈⇒≡ (sym≈ w)
  univ-sym≈ {X}{Y} w = inverse-unique p q lem-inv
    where
      p : X ≡ Y
      p = ≈⇒≡ w

      q : Y ≡ X
      q = ≈⇒≡ (sym≈ w)

      p-β : coerce p ≡ apply≈ w
      p-β = uni-coherence w

      q-β : coerce q ≡ invert≈ w
      q-β = uni-coherence (sym≈ w)

      lem : coerce (p ⊚ q) ≡ coerce refl
      lem = coerce-hom p q
          ⊚ (cong (λ h → coerce q ∘ h) p-β
          ⊚ cong (λ h → h ∘ apply≈ w) q-β
          ⊚ ext (_≅_.iso₁ (≈⇒≅ w)))

      lem-inv : p ⊚ q ≡ refl
      lem-inv = iso⇒inj uni-iso (apply≈-inj lem)
