{-# OPTIONS --without-K --type-in-type #-}
module hott.hlevel.closure.extra where

open import decidable
open import sum
open import equality.core
open import equality.calculus
open import function.core using (_∘_; const)
open import function.extensionality
open import function.isomorphism
open import sets.bool
open import sets.unit
open import sets.nat.core
open import sets.nat.ordering.leq.core
open import hott.hlevel.core
open import hott.hlevel.sets
open import hott.hlevel.closure.core
open import hott.weak-equivalence.core
  using (weak-equiv; _≈_)
open import hott.univalence
open import sets.empty

abstract
  -- Π preserves h-levels
  Π-hlevel : ∀ {n} {X : Set}{Y : X → Set}
           → ((x : X) → h n (Y x))
           → h n ((x : X) → Y x)
  Π-hlevel {n = 0} c = Π-contr c
  Π-hlevel {n = suc n} {X = X}{Y} hn = λ f g →
    subst (h n) strong-funext (Π-hlevel (λ x → hn x (f x) (g x)))

  -- Σ preserves h-levels
  Σ-hlevel : ∀ {n} {X : Set}{Y : X → Set}
           → h n X → ((x : X) → h n (Y x))
           → h n (Σ X Y)
  Σ-hlevel {n = 0}{X = X}{Y} (x₀ , cx) hy =
    (x₀ , proj₁ (hy x₀)) , λ { (x , y) → c x y }
    where
      c : (x : X)(y : Y x) → (x₀ , proj₁ (hy x₀)) ≡ (x , y)
      c x y = ap (λ x → (x , proj₁ (hy x))) (cx x)
            · ap (_,_ x) (proj₂ (hy x) y)
  Σ-hlevel {n = suc n} hx hy = λ a b → iso-hlevel Σ-split-iso
    (Σ-hlevel (hx _ _) (λ p → hy (proj₁ b) _ _))

  -- × preserves h-levels
  ×-hlevel : ∀ {n}{X : Set}{Y : Set}
           → h n X → h n Y → h n (X × Y)
  ×-hlevel hx hy = Σ-hlevel hx (λ _ → hy)

  -- ⊎ preserves h-levels
  ⊎-hlevel : ∀ {n}{X : Set}{Y : Set}
           → 2 ≤ n → h n X → h n Y → h n (X ⊎ Y)
  ⊎-hlevel {n} {X}{Y} p hx hy = iso-hlevel lem
    (Σ-hlevel (h! {p = decide p} bool-set) P-hlevel)
    where
      P : Bool → Set
      P true = X
      P false = Y

      P-hlevel : (b : Bool) → h n (P b)
      P-hlevel true = hx
      P-hlevel false = hy

      lem : Σ Bool P ≅ (X ⊎ Y)
      lem = iso f g H K
        where
          f : (Σ Bool P) → (X ⊎ Y)
          f (true , x) = inj₁ x
          f (false , y) = inj₂ y

          g : (X ⊎ Y) → (Σ Bool P)
          g (inj₁ x) = (true , x)
          g (inj₂ y) = (false , y)

          H : (x : Σ Bool P) → g (f x) ≡ x
          H (true , x) = refl
          H (false , y) = refl

          K : (x : X ⊎ Y) → f (g x) ≡ x
          K (inj₁ x) = refl
          K (inj₂ y) = refl

  Π-hlevel-impl : ∀ {n} {X : Set}{Y : X → Set}
                → ((x : X) → h n (Y x))
                → h n ({x : X} → Y x)
  Π-hlevel-impl {X = X}{Y} hY = iso-hlevel impl-iso (Π-hlevel hY)

  -- being contractible is a proposition
  contr-h1 : (X : Set) → h 1 (contr X)
  contr-h1 X = prop⇒h1 λ { (x₀ , c₀) (x₁ , c₁) →
      unapΣ (c₀ x₁ , contr⇒prop (lem (x₀ , c₀) x₁) _ _) }
    where
      lem : {A : Set} → contr A → (x : A) → contr ((x' : A) → x ≡ x')
      lem c x = Π-hlevel (λ x' → h↑ c x x')

  -- being of h-level n is a proposition
  hn-h1 : ∀ n (X : Set) → h 1 (h n X)
  hn-h1 0 X = contr-h1 X
  hn-h1 (suc n) X = Π-hlevel λ x → Π-hlevel λ y → hn-h1 n (x ≡ y)

  -- being a weak equivalence is a proposition
  weak-equiv-h1 : {X : Set}{Y : Set}
                → (f : X → Y)
                → h 1 (weak-equiv f)
  weak-equiv-h1 f = Π-hlevel λ y
                  → contr-h1 _

  ⊎-h1 : {A : Set}{B : Set}
       → h 1 A → h 1 B → ¬ (A × B)
       → h 1 (A ⊎ B)
  ⊎-h1 {A = A}{B = B} hA hB u = prop⇒h1 ⊎-prop
    where
      ⊎-prop : prop (A ⊎ B)
      ⊎-prop (inj₁ a) (inj₁ a') = ap inj₁ (h1⇒prop hA a a')
      ⊎-prop (inj₁ a) (inj₂ b') = ⊥-elim (u (a , b'))
      ⊎-prop (inj₂ b) (inj₁ a') = ⊥-elim (u (a' , b))
      ⊎-prop (inj₂ b) (inj₂ b') = ap inj₂ (h1⇒prop hB b b')

  inj-hlevel : ∀ {n} {A : Set}{B : Set}
             → (f : A → B)
             → h (suc n) A → h n (injective f)
  inj-hlevel f hA
    = Π-hlevel-impl λ x
    → Π-hlevel-impl λ x'
    → Π-hlevel λ p
    → hA x x'

  ↣-hlevel : ∀ {n}{A : Set}{B : Set}
           → h (suc n) A → h n B → h n (A ↣ B)
  ↣-hlevel hA hB
    = Σ-hlevel (Π-hlevel λ _ → hB) λ f
    → inj-hlevel f hA

  ¬-h1 : {X : Set} → h 1 (¬ X)
  ¬-h1 = Π-hlevel λ _ → ⊥-prop
