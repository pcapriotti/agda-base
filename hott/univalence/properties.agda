{-# OPTIONS --without-K #-}
module hott.univalence.properties where

open import sum
open import level using (lsuc; ↑; lift)
open import equality.core
open import equality.calculus
open import function using (_∘_; const)
open import function.extensionality.core
open import function.isomorphism
open import sets.unit
open import hott.hlevel using (contr)
open import hott.hlevel.properties.sets using (⊤-contr)
open import hott.weak-equivalence using (_≈_)
open import hott.coherence
open import hott.univalence

-- isomorphism implies equality
≅⇒≡ : ∀ {i}{X Y : Set i} → X ≅ Y → X ≡ Y
≅⇒≡ isom = ≈⇒≡ (≅⇒≈ isom)

-- any two contractible types are equal
contr-contr : ∀ {i} {X Y : Set i}
            → contr X → contr Y
            → X ≡ Y
contr-contr {X = X}{Y = Y} (x , cx) (y , cy) =
  ≅⇒≡ (iso (const y) (const x) cx cy)

-- a retract of a contractible type is contractible
retract-contr : ∀ {i j} {X : Set i}{Y : Set j}
              → (f : X → Y)(g : Y → X)
              → ((y : Y) → f (g y) ≡ y)
              → contr X → contr Y
retract-contr {Y = Y} f g r (x , c) = (f x , c')
  where
    c' : (y : Y) → f x ≡ y
    c' y = cong f (c (g y)) ⊚ r y

-- lifting preserves contractibility
↑-contr : ∀ {i} j {X : Set i}
        → contr X
        → contr (↑ j X)
↑-contr j {X} (x , cx) = lift x , lift-cx
  where
    lift-cx : (l : ↑ j X) → lift x ≡ l
    lift-cx (lift x') = cong lift (cx x')

-- exponentials preserve contractibility (given extensionality)
exp-contr : ∀ {i j}{X : Set i}{Y : Set j}
          → Extensionality i j
          → contr Y → contr (X → Y)
exp-contr {X = X} {Y = Y} ext (y , c) = (const y , c')
  where
    c' : (u : X → Y) → const y ≡ u
    c' u = ext _ _ (c ∘ u)

-- Π preserves contractibility (given extensionality)
Π-contr : ∀ {i j}{X : Set i}{Y : X → Set j}
        → (∀ {i j} → Extensionality i j)
        → ((x : X) → contr (Y x))
        → contr ((x : X) → Y x)
Π-contr {i}{j}{X} {Y} ext f =
  subst (λ z → contr ((x : X) → z x)) trivial≡Y trivial-contr
  where
    Z : Set j
    Z = ↑ j ⊤

    Z-contr : contr Z
    Z-contr = ↑-contr j ⊤-contr

    trivial : X → Set j
    trivial _ = Z

    trivial≡Y : trivial ≡ Y
    trivial≡Y = ext _ _ (λ x → contr-contr Z-contr (f x))

    trivial-contr : contr ((x : X) → trivial x)
    trivial-contr = exp-contr ext Z-contr

-- any property is preserved by isomorphism
iso-subst : ∀ {i j} {X : Set i}{Y : Set i}
           → (P : Set i → Set j)
           → X ≅ Y → P X → P Y
iso-subst P isom = subst P (≅⇒≡ isom)