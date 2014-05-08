{-# OPTIONS --without-K --type-in-type #-}
module function.extensionality.proof where

open import sum
open import equality
open import function.extensionality.core
open import hott.univalence
open import hott.hlevel.core
open import hott.hlevel.sets
open import hott.hlevel.closure.core
open import hott.weak-equivalence.core
open import sets.unit

-- this uses definitional η for ⊤
contr-exp-⊤ : {A : Set} → contr (A → ⊤)
contr-exp-⊤ = (λ _ → tt) , (λ f → refl)

module Weak where
  →-contr : {A : Set}{B : Set}
          → contr B
          → contr (A → B)
  →-contr {A = A}{B = B} hB = subst contr p contr-exp-⊤
    where
      p : (A → ⊤) ≡ (A → B)
      p = ap (λ X → A → X) (unique-contr ⊤-contr hB)

  funext : {A : Set}{B : Set}
      → (f : A → B)(b : B)(h : (x : A) → b ≡ f x)
      → (λ _ → b) ≡ f
  funext f b h =
    ap (λ u x → proj₁ (u x))
         (contr⇒prop (→-contr (singl-contr b))
                      (λ _ → (b , refl))
                      (λ x → f x , h x))

abstract
  Π-contr : {A : Set}{B : A → Set}
          → ((x : A) → contr (B x))
          → contr ((x : A) → B x)
  Π-contr {A}{B} hB = subst contr p contr-exp-⊤
    where
      p₀ : (λ _ → ⊤) ≡ B
      p₀ = Weak.funext B ⊤ (λ x → unique-contr ⊤-contr (hB x))

      p : (A → ⊤) ≡ ((x : A) → B x)
      p = ap (λ Z → (x : A) → Z x) p₀

  private
    funext₀ : Extensionality'
    funext₀ {X = X}{Y = Y}{f = f}{g = g} h = ap (λ u x → proj₁ (u x)) lem
      where
        C : X → Set
        C x = Σ (Y x) λ y → f x ≡ y

        f' g' : (x : X) → C x
        f' x = (f x , refl)
        g' x = (g x , h x)

        lem : f' ≡ g'
        lem = contr⇒prop (Π-contr (λ x → singl-contr (f x))) f' g'

abstract
  funext : Extensionality'
  funext h = funext₀ h · sym (funext₀ (λ _ → refl))

  funext-id : {X : Set}{Y : X → Set}
         → (f : (x : X) → Y x)
         → funext (λ x → refl {x = f x}) ≡ refl
  funext-id _ = left-inverse (funext₀ (λ _ → refl))
