{-# OPTIONS --without-K #-}
module equality.groupoid where

open import equality.core

_⁻¹ : {X : Set}{x y : X} → x ≡ y → y ≡ x
_⁻¹ = sym

_·_ : {X : Set}{x y z : X}
    → x ≡ y → y ≡ z → x ≡ z
_·_ = trans
infixl 9 _·_

left-unit : {X : Set}{x y : X}
          → (p : x ≡ y)
          → p · refl ≡ p
left-unit refl = refl

right-unit : {X : Set}{x y : X}
           → (p : x ≡ y)
           → refl · p ≡ p
right-unit refl = refl

associativity : {X : Set}{x y z w : X}
              → (p : x ≡ y)(q : y ≡ z)(r : z ≡ w)
              → p · q · r ≡ p · (q · r)
associativity refl _ _ = refl

left-inverse : {X : Set}{x y : X}
             → (p : x ≡ y)
             → p · p ⁻¹ ≡ refl
left-inverse refl = refl

right-inverse : {X : Set}{x y : X}
              → (p : x ≡ y)
              → p ⁻¹ · p ≡ refl
right-inverse refl = refl
