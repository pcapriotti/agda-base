{-# OPTIONS --without-K #-}
module function.isomorphism.two-out-of-six where

open import sum
open import equality
open import function.core
open import function.isomorphism.core
open import function.overloading
open import hott.equivalence.core
open import hott.equivalence.biinvertible

module two-out-of-six
         {i j k l}{X : Set i}{Y : Set j}{Z : Set k}{W : Set l}
         (f : X → Y)(g : Y → Z)(h : Z → W)
         (gf-equiv : weak-equiv (g ∘ f))
         (hg-equiv : weak-equiv (h ∘ g)) where
  private
    r : X ≅ Z
    r = ≈⇒≅ (g ∘ f , gf-equiv)

    s : Y ≅ W
    s = ≈⇒≅ (h ∘ g , hg-equiv)

    gl : Z → Y
    gl = invert s ∘ h

    gr : Z → Y
    gr = f ∘ invert r

  g-iso : Y ≅ Z
  g-iso = b⇒≅ (g , (gl , _≅_.iso₁ s) , (gr , _≅_.iso₂ r))

  f-iso : X ≅ Y
  f-iso = record
    { to = f
    ; from = λ y → invert r (g y)
    ; iso₁ = _≅_.iso₁ r
    ; iso₂ = λ y → sym (_≅_.iso₁ g-iso (f (invert r (g y))))
                 · ap (invert g-iso) (_≅_.iso₂ r (g y))
                 · _≅_.iso₁ g-iso y }

  h-iso : Z ≅ W
  h-iso = record
    { to = h
    ; from = λ w → g (invert s w)
    ; iso₁ = λ z → sym (ap (λ z → g (invert s (h z))) (_≅_.iso₂ g-iso z))
                 · ap g (_≅_.iso₁ s (invert g-iso z))
                 · _≅_.iso₂ g-iso z
    ; iso₂ = _≅_.iso₂ s }
