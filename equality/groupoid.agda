{-# OPTIONS --without-K #-}
module equality.groupoid where

open import equality.core using (_≡_ ; refl)
open import function using (id)

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

cong : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {i j} {A : Set i}{x y : A}
      → (B : A → Set j) → x ≡ y
      → B x → B y
subst B refl = id