{-# OPTIONS --without-K #-}
module function.extensionality.proof where

open import level
open import sum
open import equality
open import function.extensionality.core
open import hott.univalence
open import hott.hlevel.core
open import hott.weak-equivalence.core
open import sets.unit

top : ∀ {i} → Set i
top = ↑ _ ⊤

top-contr : ∀ {i} → contr (top {i})
top-contr = lift tt , λ _ → refl

contr-prod : ∀ {i j}{A : Set i}{B : Set j}
           → contr A → contr B
           → contr (A × B)
contr-prod (a₀ , ca) (b₀ , cb)
  = (a₀ , b₀)
  , λ {(x , y) → cong₂ _,_ (ca x) (cb y) }

-- this uses definitional η for ⊤
contr-exp-⊤ : ∀ {i j}{A : Set i} → contr (A → top {j})
contr-exp-⊤ = (λ _ → lift tt) , (λ f → refl)

unique-contr : ∀ {i}{A : Set i} → contr A → top ≡ A
unique-contr {i}{A} hA = ≈⇒≡ (f , f-we)
  where
    f : top → A
    f _ = proj₁ hA

    f-we : weak-equiv f
    f-we a = contr-prod top-contr (h↑ hA _ _)

module Weak where
  →-contr : ∀ {i j}{A : Set i}{B : Set j}
          → contr B
          → contr (A → B)
  →-contr {A = A}{B = B} hB = subst contr p contr-exp-⊤
    where
      p : (A → top) ≡ (A → B)
      p = cong (λ X → A → X) (unique-contr hB)

  ext : ∀ {i j}{A : Set i}{B : Set j}
      → (f : A → B)(b : B)(h : (x : A) → b ≡ f x)
      → (λ _ → b) ≡ f
  ext f b h =
    cong (λ u x → proj₁ (u x))
         (contr⇒prop (→-contr (singl-contr b))
                      (λ _ → (b , refl))
                      (λ x → f x , h x))
private
  abstract
    Π-contr : ∀ {i j}{A : Set i}{B : A → Set j}
            → ((x : A) → contr (B x))
            → contr ((x : A) → B x)
    Π-contr {i}{j}{A}{B} hB = subst contr p contr-exp-⊤
      where
        p₀ : (λ _ → top) ≡ B
        p₀ = Weak.ext B top (λ x → unique-contr (hB x))

        p : (A → top {j}) ≡ ((x : A) → B x)
        p = cong (λ Z → (x : A) → Z x) p₀

    ext₀ : ∀ {i j} → Extensionality' i j
    ext₀ {i}{j}{X = X}{Y = Y}{f = f}{g = g} h = cong (λ u x → proj₁ (u x)) lem
      where
        C : X → Set j
        C x = Σ (Y x) λ y → f x ≡ y

        f' g' : (x : X) → C x
        f' x = (f x , refl)
        g' x = (g x , h x)

        lem : f' ≡ g'
        lem = contr⇒prop (Π-contr (λ x → singl-contr (f x))) f' g'

abstract
  ext : ∀ {i j} → Extensionality' i j
  ext h = ext₀ h ⊚ sym (ext₀ (λ _ → refl))

  ext-id : ∀ {i j}{X : Set i}{Y : X → Set j}
         → (f : (x : X) → Y x)
         → ext (λ x → refl {x = f x}) ≡ refl
  ext-id _ = left-inverse (ext₀ (λ _ → refl))
