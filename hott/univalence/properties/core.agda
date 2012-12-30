{-# OPTIONS --without-K #-}
module hott.univalence.properties.core where

open import sum
open import level using (lsuc; ↑; lift)
open import equality.core
open import equality.calculus
open import equality.isomorphisms.core
open import function using (_∘_; const)
open import function.extensionality.core
open import function.isomorphism
open import function.isomorphism.properties
open import sets.unit
open import sets.nat using (ℕ; suc)
open import hott.hlevel using (h; contr)
open import hott.hlevel.properties.sets using (⊤-contr)
open import hott.weak-equivalence using (_≈_)
open import hott.coherence
open import hott.univalence

abstract
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

  -- lifting preserves h-levels
  ↑-contr : ∀ {i n} j {X : Set i}
          → h n X
          → h n (↑ j X)
  ↑-contr j {X} = iso-h (lift-iso j X)

  -- exponentials preserve contractibility (given extensionality)
  exp-contr : ∀ {i j}{X : Set i}{Y : Set j}
            → Extensionality i j
            → contr Y → contr (X → Y)
  exp-contr {X = X} {Y = Y} ext (y , c) = (const y , c')
    where
      c' : (u : X → Y) → const y ≡ u
      c' u = ext (c ∘ u)

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
      trivial≡Y = ext (λ x → contr-contr Z-contr (f x))

      trivial-contr : contr ((x : X) → trivial x)
      trivial-contr = exp-contr ext Z-contr

  -- Π preserves h-levels
  Π-hlevel : ∀ {i j n} {X : Set i}{Y : X → Set j}
           → (∀ {i j} → StrongExt i j)
           → ((x : X) → h n (Y x))
           → h n ((x : X) → Y x)
  Π-hlevel {n = 0} ext c = Π-contr (coerce ext) c
  Π-hlevel {n = suc n} {X = X}{Y} ext hn = λ f g →
    subst (h n) ext (Π-hlevel ext (λ x → hn x (f x) (g x)))

  -- Σ preserves h-levels
  Σ-hlevel : ∀ {i j n} {X : Set i}{Y : X → Set j}
           → h n X → ((x : X) → h n (Y x))
           → h n (Σ X Y)
  Σ-hlevel {n = 0}{X = X}{Y} (x₀ , cx) hy =
    (x₀ , proj₁ (hy x₀)) , λ { (x , y) → c x y }
    where
      c : (x : X)(y : Y x) → (x₀ , proj₁ (hy x₀)) ≡ (x , y)
      c x y = cong (λ x → (x , proj₁ (hy x))) (cx x)
            ⊚ cong (_,_ x) (proj₂ (hy x) y)
  Σ-hlevel {n = suc n} hx hy = λ a b → iso-h Σ-split-iso
    (Σ-hlevel (hx _ _) (λ p → hy (proj₁ b) _ _))

  -- × preserves h-levels
  ×-hlevel : ∀ {i j n}{X : Set i}{Y : Set j}
           → h n X → h n Y → h n (X × Y)
  ×-hlevel hx hy = Σ-hlevel hx (λ _ → hy)

  -- any property is preserved by isomorphism
  iso-subst : ∀ {i j} {X : Set i}{Y : Set i}
             → (P : Set i → Set j)
             → X ≅ Y → P X → P Y
  iso-subst P isom = subst P (≅⇒≡ isom)
