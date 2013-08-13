{-# OPTIONS --without-K #-}
module hott.weak-equivalence.core where

open import equality.core using (_≡_ ; refl ; ap)
open import sum using (Σ ; proj₁ ; proj₂ ; _,_)
open import level using (_⊔_)
open import hott.hlevel.core using (contr ; prop ; _⁻¹_)
open import function.core using (_$_)
open import function.isomorphism.core using (_≅_ ; iso)

-- a function is a weak equivalence, if the inverse images of all points are contractible
weak-equiv : ∀ {i k} {X : Set i} {Y : Set k} (f : X → Y) → Set (i ⊔ k)
weak-equiv {_} {_} {X} {Y} f = (y : Y) → contr $ f ⁻¹ y

-- weak equivalences
_≈_ : ∀ {i j} (X : Set i) (Y : Set j) → Set _
X ≈ Y = Σ (X → Y) λ f → weak-equiv f

apply≈ : ∀ {i j} {X : Set i}{Y : Set j} → X ≈ Y → X → Y
apply≈ = proj₁

≈⇒≅ : ∀ {i j} {X : Set i} {Y : Set j} → X ≈ Y → X ≅ Y
≈⇒≅ {X = X}{Y} (f , we) = iso f g iso₁ iso₂
  where
    g : Y → X
    g y = proj₁ (proj₁ (we y))

    iso₁ : (x : X) → g (f x) ≡ x
    iso₁ x = ap proj₁ (proj₂ (we (f x)) (x , refl))

    iso₂ : (y : Y) → f (g y) ≡ y
    iso₂ y = proj₂ (proj₁ (we y))

invert≈ : ∀ {i j} {X : Set i}{Y : Set j} → X ≈ Y → Y → X
invert≈ (_ , we) y = proj₁ (proj₁ (we y))
