{-# OPTIONS --without-K --type-in-type #-}
module hott.weak-equivalence.core where

open import equality.core using (_≡_ ; refl ; cong)
open import sum using (Σ ; proj₁ ; proj₂ ; _,_)
open import level using (_⊔_)
open import hott.hlevel.core using (contr ; prop ; _⁻¹_)
open import function.core using (_$_)
open import function.isomorphism.core using (_≅_ ; iso)

-- a function is a weak equivalence, if the inverse images of all points are contractible
weak-equiv : {X Y : Set} (f : X → Y) → Set
weak-equiv {X}{Y} f = (y : Y) → contr $ f ⁻¹ y

-- weak equivalences
_≈_ : (X Y : Set) → Set
X ≈ Y = Σ (X → Y) λ f → weak-equiv f

apply≈ : {X Y : Set} → X ≈ Y → X → Y
apply≈ = proj₁

≈⇒≅ : {X Y : Set} → X ≈ Y → X ≅ Y
≈⇒≅ {X = X}{Y} (f , we) = iso f g iso₁ iso₂
  where
    g : Y → X
    g y = proj₁ (proj₁ (we y))

    iso₁ : (x : X) → g (f x) ≡ x
    iso₁ x = cong proj₁ (proj₂ (we (f x)) (x , refl))

    iso₂ : (y : Y) → f (g y) ≡ y
    iso₂ y = proj₂ (proj₁ (we y))

invert≈ : {X Y : Set} → X ≈ Y → Y → X
invert≈ (_ , we) y = proj₁ (proj₁ (we y))
