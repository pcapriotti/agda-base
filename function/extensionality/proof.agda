{-# OPTIONS --without-K #-}
module function.extensionality.proof where

open import level
open import sum
open import equality
open import function.extensionality.core
open import hott.univalence
open import hott.level.core
open import hott.level.closure.core
open import hott.level.sets.core
open import hott.equivalence.core
open import sets.unit

-- this uses definitional η for ⊤
contr-exp-⊤ : ∀ {i j}{A : Set i} → contr (A → ⊤ {j})
contr-exp-⊤ = (λ _ → tt) , (λ f → refl)

module Weak where
  →-contr : ∀ {i j}{A : Set i}{B : Set j}
          → contr B
          → contr (A → B)
  →-contr {A = A}{B = B} hB = subst contr p contr-exp-⊤
    where
      p : (A → ⊤) ≡ (A → B)
      p = ap (λ X → A → X) (unique-contr ⊤-contr hB)

  funext : ∀ {i j}{A : Set i}{B : Set j}
      → (f : A → B)(b : B)(h : (x : A) → b ≡ f x)
      → (λ _ → b) ≡ f
  funext f b h =
    ap (λ u x → proj₁ (u x))
         (contr⇒prop (→-contr (singl-contr b))
                      (λ _ → (b , refl))
                      (λ x → f x , h x))

abstract
  Π-contr : ∀ {i j}{A : Set i}{B : A → Set j}
          → ((x : A) → contr (B x))
          → contr ((x : A) → B x)
  Π-contr {i}{j}{A}{B} hB = subst contr p contr-exp-⊤
    where
      p₀ : (λ _ → ⊤) ≡ B
      p₀ = Weak.funext B ⊤ (λ x → unique-contr ⊤-contr (hB x))

      p : (A → ⊤ {j}) ≡ ((x : A) → B x)
      p = ap (λ Z → (x : A) → Z x) p₀

  private
    funext₀ : ∀ {i j} → Extensionality' i j
    funext₀ {i}{j}{X = X}{Y = Y}{f = f}{g = g} h = ap (λ u x → proj₁ (u x)) lem
      where
        C : X → Set j
        C x = Σ (Y x) λ y → f x ≡ y

        f' g' : (x : X) → C x
        f' x = (f x , refl)
        g' x = (g x , h x)

        lem : f' ≡ g'
        lem = contr⇒prop (Π-contr (λ x → singl-contr (f x))) f' g'

abstract
  funext : ∀ {i j} → Extensionality' i j
  funext h = funext₀ h · sym (funext₀ (λ _ → refl))

  funext-id : ∀ {i j}{X : Set i}{Y : X → Set j}
         → (f : (x : X) → Y x)
         → funext (λ x → refl {x = f x}) ≡ refl
  funext-id _ = left-inverse (funext₀ (λ _ → refl))
