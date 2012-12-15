{-# OPTIONS --without-K #-}
module function.isomorphism where

open import level using (_⊔_)
open import equality.core
open import equality.groupoid
open import equality.reasoning
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
