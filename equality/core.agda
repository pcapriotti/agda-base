{-# OPTIONS --without-K #-}
module equality.core where

open import sum
open import function.core

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

ap : {A : Set}{B : Set}{x y : A}
   → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

ap₂ : {A : Set}{B : Set}{C : Set}
        {x x' : A}{y y' : B}
      → (f : A → B → C)
      → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂ f refl refl = refl

subst : {A : Set}{x y : A}
      → (B : A → Set) → x ≡ y
      → B x → B y
subst B refl = id

subst₂ : {A : Set}{x x' : A}
         {B : Set}{y y' : B}
       → (C : A → B → Set)
       → x ≡ x' → y ≡ y'
       → C x y → C x' y'
subst₂ C refl refl = id

singleton : {A : Set} → A → Set
singleton {A = A} a = Σ A λ a' → a ≡ a'

singleton' : {A : Set} → A → Set
singleton' {A = A} a = Σ A λ a' → a' ≡ a

J' : {X : Set}{x : X}
   → (P : (y : X) → x ≡ y → Set)

   → P x refl
   → (y : X)
   → (p : x ≡ y)
   → P y p
J' P u y refl = u

J : {X : Set}
  → (P : (x y : X) → x ≡ y → Set)
  → ((x : X) → P x x refl)
  → (x y : X)
  → (p : x ≡ y)
  → P x y p
J P u x y p = J' (P x) (u x) y p
