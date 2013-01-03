{-# OPTIONS --without-K #-}
module hott.univalence.properties.core where

open import level
open import decidable
open import sum
open import level using (lsuc; ↑; lift)
open import equality.core
open import equality.calculus
open import equality.isomorphisms
open import function using (_∘_; const)
open import function.extensionality.core
open import function.isomorphism
open import function.isomorphism.properties
open import sets.bool
open import sets.unit
open import sets.nat using (ℕ; suc; _≤?_)
open import hott.hlevel
open import hott.hlevel.properties using (⊤-contr; bool-set; h!)
open import hott.weak-equivalence.core using (_≈_)
open import hott.univalence

abstract
  -- any two contractible types are equal
  contr-contr : ∀ {i} {X Y : Set i}
              → contr X → contr Y
              → X ≡ Y
  contr-contr {X = X}{Y = Y} (x , cx) (y , cy) = ≈⇒≡ (f , we)
    where
      f : X → Y
      f _ = y

      K : (y' : Y) → f x ≡ y'
      K = cy

      cy-y : cy y ≡ refl
      cy-y = proj₁ (h↑ (h↑ (y , cy)) y y (cy y) refl)

      lem : (y' : Y)(x' : f ⁻¹ y')
          → (x , K y') ≡ x'
      lem .(f x') (x' , refl) =
        uncongΣ (cx x' , subst-const (cx x') (cy y) ⊚ cy-y)

      we : (y' : Y) → contr (f ⁻¹ y')
      we y' = (x , K y') , lem y'

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
  ↑-contr : ∀ {i n} j {X : Set i}
          → h n X
          → h n (↑ j X)
  ↑-contr j {X} = iso-hlevel (lift-iso j X)

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
  Σ-hlevel {n = suc n} hx hy = λ a b → iso-hlevel Σ-split-iso
    (Σ-hlevel (hx _ _) (λ p → hy (proj₁ b) _ _))

  -- × preserves h-levels
  ×-hlevel : ∀ {i j n}{X : Set i}{Y : Set j}
           → h n X → h n Y → h n (X × Y)
  ×-hlevel hx hy = Σ-hlevel hx (λ _ → hy)

  -- ⊎ preserves h-levels
  ⊎-hlevel : ∀ {i j n}{X : Set i}{Y : Set j}
           → {p : True (2 ≤? n)}
           → h n X → h n Y → h n (X ⊎ Y)
  ⊎-hlevel {i}{j}{n} {X}{Y} {p} hx hy = iso-hlevel lem
    (Σ-hlevel (h! {p = p} bool-set) P-hlevel)
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
