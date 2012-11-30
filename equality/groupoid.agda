{-# OPTIONS --without-K #-}
module equality.groupoid where

open import equality.core

sym : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {i} {A : Set i} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

_⁻¹ : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
_⁻¹ = sym
infix 6 _⁻¹

_⊚_ : ∀ {i} {A : Set i} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
_⊚_ = trans
infixl 5 _⊚_