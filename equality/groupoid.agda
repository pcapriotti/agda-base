{-# OPTIONS --without-K #-}
module equality.groupoid where

open import equality.core

_⁻¹ : ∀ {i}{X : Set i}{x y : X} → x ≡ y → y ≡ x
_⁻¹ = sym

_·_ : ∀ {i}{X : Set i}{x y z : X}
    → x ≡ y → y ≡ z → x ≡ z
_·_ = trans
infixl 9 _·_

left-unit : ∀ {i}{X : Set i}{x y : X}
          → (p : x ≡ y)
          → p · refl ≡ p
left-unit refl = refl

right-unit : ∀ {i}{X : Set i}{x y : X}
           → (p : x ≡ y)
           → refl · p ≡ p
right-unit refl = refl

associativity : ∀ {i}{X : Set i}{x y z w : X}
              → (p : x ≡ y)(q : y ≡ z)(r : z ≡ w)
              → p · q · r ≡ p · (q · r)
associativity refl _ _ = refl

left-inverse : ∀ {i}{X : Set i}{x y : X}
             → (p : x ≡ y)
             → p · p ⁻¹ ≡ refl
left-inverse refl = refl

right-inverse : ∀ {i}{X : Set i}{x y : X}
              → (p : x ≡ y)
              → p ⁻¹ · p ≡ refl
right-inverse refl = refl
