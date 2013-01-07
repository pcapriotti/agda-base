{-# OPTIONS --without-K #-}
module hott.hlevel.closure where

open import level
open import decidable
open import sum
open import level using (lsuc; ↑; lift)
open import equality.core
open import equality.calculus
open import function using (_∘_; const)
open import function.extensionality
open import function.isomorphism
open import sets.bool
open import sets.unit
open import sets.nat using (ℕ; suc; _≤_)
open import hott.hlevel.core
open import hott.hlevel.sets using (⊤-contr; bool-set)
open import hott.hlevel.properties
open import hott.weak-equivalence.core
  using (weak-equiv; _≈_)
open import hott.univalence

abstract
  -- Π preserves h-levels
  Π-hlevel : ∀ {i j n} {X : Set i}{Y : X → Set j}
           → ((x : X) → h n (Y x))
           → h n ((x : X) → Y x)
  Π-hlevel {n = 0} c = Π-contr c
  Π-hlevel {n = suc n} {X = X}{Y} hn = λ f g →
    subst (h n) strong-ext (Π-hlevel (λ x → hn x (f x) (g x)))

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
  Σ-hlevel {n = suc n} hx hy = λ a b → iso-hlevel Σ-split-iso
    (Σ-hlevel (hx _ _) (λ p → hy (proj₁ b) _ _))

  -- × preserves h-levels
  ×-hlevel : ∀ {i j n}{X : Set i}{Y : Set j}
           → h n X → h n Y → h n (X × Y)
  ×-hlevel hx hy = Σ-hlevel hx (λ _ → hy)

  -- ⊎ preserves h-levels
  ⊎-hlevel : ∀ {i j n}{X : Set i}{Y : Set j}
           → 2 ≤ n → h n X → h n Y → h n (X ⊎ Y)
  ⊎-hlevel {i}{j}{n} {X}{Y} p hx hy = iso-hlevel lem
    (Σ-hlevel (h! {p = decide p} bool-set) P-hlevel)
    where
      P : Bool → Set (i ⊔ j)
      P true = ↑ j X
      P false = ↑ i Y

      P-hlevel : (b : Bool) → h n (P b)
      P-hlevel true = iso-hlevel (lift-iso j X) hx
      P-hlevel false = iso-hlevel (lift-iso i Y) hy

      lem : Σ Bool P ≅ (X ⊎ Y)
      lem = iso f g H K
        where
          f : (Σ Bool P) → (X ⊎ Y)
          f (true , lift x) = inj₁ x
          f (false , lift y) = inj₂ y

          g : (X ⊎ Y) → (Σ Bool P)
          g (inj₁ x) = (true , lift x)
          g (inj₂ y) = (false , lift y)

          H : (x : Σ Bool P) → g (f x) ≡ x
          H (true , lift x) = refl
          H (false , lift y) = refl

          K : (x : X ⊎ Y) → f (g x) ≡ x
          K (inj₁ x) = refl
          K (inj₂ y) = refl

  Π-hlevel-impl : ∀ {i j n} {X : Set i}{Y : X → Set j}
                → ((x : X) → h n (Y x))
                → h n ({x : X} → Y x)
  Π-hlevel-impl {X = X}{Y} hY = iso-hlevel impl-iso (Π-hlevel hY)

  -- being contractible is a proposition
  contr-h1 : ∀ {i}(X : Set i) → h 1 (contr X)
  contr-h1 X = prop⇒h1 λ { (x₀ , c₀) (x₁ , c₁) →
      uncongΣ (c₀ x₁ , contr⇒prop (lem (x₀ , c₀) x₁) _ _) }
    where
      lem : ∀ {i}{A : Set i} → contr A → (x : A) → contr ((x' : A) → x ≡ x')
      lem c x = Π-hlevel (λ x' → h↑ c x x')

  -- being of h-level n is a proposition
  hn-h1 : ∀ {i} n (X : Set i) → h 1 (h n X)
  hn-h1 0 X = contr-h1 X
  hn-h1 (suc n) X = Π-hlevel λ x → Π-hlevel λ y → hn-h1 n (x ≡ y)

  -- being a weak equivalence is a proposition
  weak-equiv-h1 : ∀ {i j}{X : Set i}{Y : Set j}
                → (f : X → Y)
                → h 1 (weak-equiv f)
  weak-equiv-h1 f = Π-hlevel λ y
                  → contr-h1 _
