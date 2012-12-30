{-# OPTIONS --without-K #-}
module equality.isomorphisms where

open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import equality.isomorphisms.core public
open import function
open import function.extensionality
open import function.isomorphism
open import hott.coherence
open import hott.univalence

Σ-split : ∀ {i j}{X : Set i}{Y : X → Set j}
        → {a a' : X}{b : Y a}{b' : Y a'}
        → (Σ (a ≡ a') λ q → subst Y q b ≡ b')
        ≡ ((a , b) ≡ (a' , b'))
Σ-split = ≅⇒≡ Σ-split-iso

Π-cong : ∀ {i j}{X : Set i}{Y Y' : X → Set j}
       → ((x : X) → Y x ≡ Y' x)
       → ((x : X) → Y x)
       ≡ ((x : X) → Y' x)
Π-cong {X = X} h = cong (λ Y → (x : X) → Y x) (ext' h)

Σ-cong : ∀ {i j}{X : Set i}{X' : Set i}{Y : X → Set j}
       → (p : X ≡ X')
       → (Σ X Y ≡ Σ X' (Y ∘ invert (≡⇒≅ p)))
Σ-cong {X = X}{.X}{Y} refl = refl

ΠΣ-swap : ∀ {i j k}{X : Set i}{Y : X → Set j}
        → {Z : (x : X) → Y x → Set k}
        → ((x : X) → Σ (Y x) λ y → Z x y)
        ≡ (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap = ≅⇒≡ ΠΣ-swap-iso
