{-# OPTIONS --without-K #-}
module function.isomorphism where

open import level using (_⊔_)
open import equality.core
open import equality.groupoid
open import equality.reasoning
open import function
open import sum
open import function.extensionality.core

-- isomorphisms
record _≅_ {i j}(X : Set i)(Y : Set j) : Set (i ⊔ j) where
  constructor iso
  field
    to : X → Y
    from : Y → X
    iso₁ : (x : X) → from (to x) ≡ x
    iso₂ : (y : Y) → to (from y) ≡ y

refl≅ : ∀ {i}{X Y : Set i} → X ≡ Y → X ≅ Y
refl≅ refl = iso id id (λ _ → refl) (λ _ → refl)

sym≅ : ∀ {i j}{X : Set i}{Y : Set j} → X ≅ Y → Y ≅ X
sym≅ (iso f g H K) = iso g f K H

trans≅ : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
       → X ≅ Y → Y ≅ Z → X ≅ Z
trans≅ (iso f g H K) (iso f' g' H' K') = record
  { to = f' ∘ f
  ; from = g ∘ g'
  ; iso₁ = λ x → cong g (H' (f x)) ⊚ H x
  ; iso₂ = λ y → cong f' (K (g' y)) ⊚ K' y }

private
  module Dummy {i j}{X : Set i}{Y : Set j} where
      isInjective : (f : X → Y) → Set _
      isInjective f = (x x' : _) → f x ≡ f x' → x ≡ x'

      isSurjective : (f : X → Y) → Set _
      isSurjective f = (y : Y) → Σ X λ x → f x ≡ y

      open _≅_ public using ()
        renaming (to to apply ; from to invert)

      iso⇒inj : (iso : X ≅ Y) → isInjective (apply iso)
      iso⇒inj f x x' q = (iso₁ x) ⁻¹ ⊚ cong from q ⊚ iso₁ x'
        where
          open _≅_ f

      iso⇒surj : (iso : X ≅ Y) → isSurjective (apply iso)
      iso⇒surj f y = from y , iso₂ y
        where
          open _≅_ f

      inj+surj⇒iso : (f : X → Y) → isInjective f → isSurjective f → X ≅ Y
      inj+surj⇒iso f inj-f surj-f = iso f g H K
        where
          g : Y → X
          g y = proj₁ (surj-f y)

          H : (x : X) → g (f x) ≡ x
          H x = inj-f (g (f x)) x (proj₂ (surj-f (f x))) 

          K : (y : Y) → f (g y) ≡ y
          K y = proj₂ (surj-f y)
open Dummy public
