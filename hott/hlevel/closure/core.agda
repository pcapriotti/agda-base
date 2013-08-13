{-# OPTIONS --without-K #-}

module hott.hlevel.closure.core where

open import level
open import decidable
open import equality
open import function.isomorphism.core
open import function.isomorphism.properties
open import sum
open import hott.hlevel.core
open import hott.hlevel.sets
open import hott.weak-equivalence.core
open import hott.univalence
open import sets.nat.core
open import sets.unit

Σ-contr : ∀ {i j}{X : Set i}{Y : X → Set j}
        → contr X → ((x : X) → contr (Y x))
        → contr (Σ X Y)
Σ-contr {X = X}{Y = Y} (x₀ , cx) hY
  = (x₀ , proj₁ (hY x₀)) , λ { (x , y) → c x y }
    where
      c : (x : X)(y : Y x) → (x₀ , proj₁ (hY x₀)) ≡ (x , y)
      c x y = cong (λ x → (x , proj₁ (hY x))) (cx x)
            ⊚ cong (_,_ x) (proj₂ (hY x) y)

×-contr : ∀ {i j}{X : Set i}{Y : Set j}
        → contr X → contr Y
        → contr (X × Y)
×-contr hX hY = Σ-contr hX (λ _ → hY)

unique-contr : ∀ {i}{A B : Set i}
             → contr A
             → contr B
             → A ≡ B
unique-contr {i}{A}{B} hA hB = ≈⇒≡ (f , f-we)
  where
    f : A → B
    f _ = proj₁ hB

    f-we : weak-equiv f
    f-we b = ×-contr hA (h↑ hB _ _)

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
