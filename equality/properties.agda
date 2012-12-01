{-# OPTIONS --without-K #-}

module equality.properties where

open import equality.core

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
