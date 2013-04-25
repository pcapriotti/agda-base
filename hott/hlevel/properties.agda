{-# OPTIONS --without-K #-}
module hott.hlevel.properties where

open import level
open import sum
open import decidable
open import equality.core
open import equality.calculus
open import sets.nat.core
open import sets.unit
open import function.core
open import function.extensionality.nondep
open import function.isomorphism.core
open import function.isomorphism.properties
open import hott.hlevel.core
open import hott.hlevel.sets
open import hott.univalence

h-≤ : ∀ {i n m}{X : Set i}
    → n ≤ m → h n X → h m X
h-≤ {m = 0} z≤n hX = hX
h-≤ {m = suc m} z≤n hX = λ x y
  → h-≤ {m = m} z≤n (h↑ hX x y)
h-≤ (s≤s p) hX = λ x y
  → h-≤ p (hX x y)

h! : ∀ {i n m}{X : Set i}
   → {p : True (n ≤? m)}
   → h n X → h m X
h! {p = p} = h-≤ (witness p)

abstract
  -- retractions preserve hlevels
  retract-hlevel : ∀ {i j n} {X : Set i}{Y : Set j}
                 → (f : X → Y)(g : Y → X)
                 → ((y : Y) → f (g y) ≡ y)
                 → h n X → h n Y
  retract-hlevel {n = 0}{X}{Y} f g r (x , c) = (f x , c')
    where
      c' : (y : Y) → f x ≡ y
      c' y = cong f (c (g y)) ⊚ r y
  retract-hlevel {n = suc n}{X}{Y} f g r hX = λ y y'
    → retract-hlevel f' g' r' (hX (g y) (g y'))
    where
      f' : {y y' : Y} → g y ≡ g y' → y ≡ y'
      f' {y}{y'} p = sym (r y) ⊚ cong f p ⊚ r y'

      g' : {y y' : Y} → y ≡ y' → g y ≡ g y'
      g' = cong g

      r' : {y y' : Y}(p : y ≡ y') → f' (g' p) ≡ p
      r' {y}{.y} refl = cong (λ α → α ⊚ r y) (left-unit (sym (r y)))
                      ⊚ right-inverse (r y)

  iso-hlevel : ∀ {i j n}{X : Set i}{Y : Set j}
             → X ≅ Y → h n X → h n Y
  iso-hlevel (iso f g H K) = retract-hlevel f g K

  -- lifting preserves h-levels
  ↑-hlevel : ∀ {i n} j {X : Set i}
          → h n X
          → h n (↑ j X)
  ↑-hlevel j {X} = iso-hlevel (lift-iso j X)

  -- any two contractible types are equal
  contr-contr : ∀ {i} {X Y : Set i} → contr X → contr Y → X ≡ Y
  contr-contr {X = X}{Y = Y} (x , cx) (y , cy) = ≈⇒≡ (f , we)
    where
      f : X → Y
      f _ = y

      K : (y' : Y) → f x ≡ y'
      K = cy

      cy-y : cy y ≡ refl
      cy-y = proj₁ (h↑ (h↑ (y , cy)) y y (cy y) refl)

      lem : (y' : Y)(x' : f ⁻¹ y') → (x , K y') ≡ x'
      lem .(f x') (x' , refl) =
        uncongΣ (cx x' , subst-const (cx x') (cy y) ⊚ cy-y)

      we : (y' : Y) → contr (f ⁻¹ y')
      we y' = (x , K y') , lem y'

  -- exponentials preserve contractibility (given extensionality)
  exp-contr : ∀ {i j}{X : Set i}{Y : Set j}
            → contr Y → contr (X → Y)
  exp-contr {X = X} {Y = Y} (y , c) = (const y , c')
    where
      c' : (u : X → Y) → const y ≡ u
      c' u = ext λ x → c (u x)

  -- Π preserves contractibility
  Π-contr : ∀ {i j}{X : Set i}{Y : X → Set j}
          → ((x : X) → contr (Y x))
          → contr ((x : X) → Y x)
  Π-contr {i}{j}{X} {Y} f =
    subst (λ z → contr ((x : X) → z x)) trivial≡Y trivial-contr
    where
      Z : Set j
      Z = ↑ j ⊤

      Z-contr : contr Z
      Z-contr = ↑-hlevel j ⊤-contr

      trivial : X → Set j
      trivial _ = Z

      trivial≡Y : trivial ≡ Y
      trivial≡Y = ext (λ x → contr-contr Z-contr (f x))

      trivial-contr : contr ((x : X) → trivial x)
      trivial-contr = exp-contr Z-contr
