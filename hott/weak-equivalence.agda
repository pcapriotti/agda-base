{-# OPTIONS --without-K #-}
module hott.weak-equivalence where

open import equality.core using (_≡_ ; refl ; cong)
open import sum using (Σ ; proj₁ ; proj₂ ; _,_)
open import level using (_⊔_)
open import hott.hlevel using (contr ; isProp ; _⁻¹_)
open import function using (_$_)
open import function.isomorphism using (_≅_ ; iso)

-- a function is a weak equivalence, if the inverse images of all points are contractible
isWeakEquiv : ∀ {i k} {X : Set i} {Y : Set k} (f : X → Y) → Set (i ⊔ k)
isWeakEquiv {_} {_} {X} {Y} f = (y : Y) → contr $ f ⁻¹ y

-- weak equivalences
_≈_ : ∀ {i j} (X : Set i) (Y : Set j) → Set _
X ≈ Y = Σ (X → Y) λ f → isWeakEquiv f

apply≈ : ∀ {i} {X Y : Set i} → X ≈ Y → X → Y
apply≈ = proj₁

≈⇒≅ : ∀ {i j} {X : Set i} {Y : Set j} → X ≈ Y → X ≅ Y
≈⇒≅ {X = X}{Y} (f , we) = iso f g iso₁ iso₂
  where
    g : Y → X
    g y = proj₁ (proj₁ (we y))

    iso₁ : (x : X) → g (f x) ≡ x
    iso₁ x = cong proj₁ (proj₂ (we (f x)) (x , refl))

    iso₂ : (y : Y) → f (g y) ≡ y
    iso₂ y = proj₂ (proj₁ (we y))

invert≈ : ∀ {i} {X Y : Set i} → X ≈ Y → Y → X
invert≈ (_ , we) y = proj₁ (proj₁ (we y))

-- being a weak equivalence is propositional
-- we-prop : ∀ {i j}{X : Set i}{Y : Set j}{f : X → Y}
--         → isProp (isWeakEquiv f)
-- we-prop = {!!}