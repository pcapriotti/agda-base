{-# OPTIONS --without-K #-}
module hott.univalence.properties where

open import sum
open import sum.properties
open import level using (lsuc; ↑; lift)
open import equality.core
open import equality.calculus
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

-- Π preserves h-levels
Π-hlevel : ∀ {i j} {X : Set i}{Y : X → Set j}
         → (∀ {i j} → StrongExt i j)
         → (n : ℕ) → ((x : X) → h n (Y x))
         → h n ((x : X) → Y x)
Π-hlevel ext 0 c = Π-contr (λ f g → coerce (ext f g)) c
Π-hlevel {X = X}{Y} ext (suc n) hn = λ f g →
  subst (h n) (ext f g) (Π-hlevel ext n (λ x → hn x (f x) (g x)))

-- Σ preserves h-levels
Σ-hlevel : ∀ {i j} {X : Set i}{Y : X → Set j}
         → (n : ℕ) → h n X
         → ((x : X) → h n (Y x))
         → h n (Σ X Y)
Σ-hlevel {X = X}{Y} 0 (x₀ , cx) hy =
  (x₀ , proj₁ (hy x₀)) , λ { (x , y) → c x y }
  where
    c : (x : X)(y : Y x) → (x₀ , proj₁ (hy x₀)) ≡ (x , y)
    c x y = cong (λ x → (x , proj₁ (hy x))) (cx x)
          ⊚ cong (_,_ x) (proj₂ (hy x) y)
Σ-hlevel (suc n) hx hy = λ a b → iso-h Σ-split-iso n
  (Σ-hlevel n (hx _ _) (λ p → hy (proj₁ b) _ _))

-- any property is preserved by isomorphism
iso-subst : ∀ {i j} {X : Set i}{Y : Set i}
           → (P : Set i → Set j)
           → X ≅ Y → P X → P Y
iso-subst P isom = subst P (≅⇒≡ isom)