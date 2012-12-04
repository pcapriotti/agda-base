{-# OPTIONS --without-K #-}

module equality.properties where

open import sum using (Σ ; _,_ ; proj₁)
open import equality.core using (_≡_ ; refl ; trans ; sym)
open import function using (_∘_)

left-unit : ∀ {i} {A : Set i}{x y : A}
          → (p : x ≡ y) → trans p refl ≡ p
left-unit refl = refl

right-unit : ∀ {i} {A : Set i}{x y : A}
           → (p : x ≡ y) → trans refl p ≡ p
right-unit refl = refl

associativity : ∀ {i} {A : Set i}{x y z w : A}
              → (p : x ≡ y)(q : y ≡ z)(r : z ≡ w)
              → trans p (trans q r)
              ≡ trans (trans p q) r
associativity refl q r = refl

left-inverse : ∀ {i} {A : Set i} {x y : A} (p : x ≡ y)
             → trans p (sym p) ≡ refl
left-inverse refl = refl

right-inverse : ∀ {i} {A : Set i} {x y : A} (p : x ≡ y)
              → trans (sym p) p ≡ refl
right-inverse refl = refl
