{-# OPTIONS --without-K #-}
module equality.core where

open import sum
open import level using ()
open import function.core

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

sym : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

_·_ : ∀ {i}{X : Set i}{x y z : X}
    → x ≡ y → y ≡ z → x ≡ z
refl · p = p
infixl 9 _·_

ap : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

ap₂ : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
        {x x' : A}{y y' : B}
      → (f : A → B → C)
      → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂ f refl refl = refl

subst : ∀ {i j} {A : Set i}{x y : A}
      → (B : A → Set j) → x ≡ y
      → B x → B y
subst B refl = id

subst₂ : ∀ {i j k} {A : Set i}{x x' : A}
         {B : Set j}{y y' : B}
       → (C : A → B → Set k)
       → x ≡ x' → y ≡ y'
       → C x y → C x' y'
subst₂ C refl refl = id

singleton : ∀ {i}{A : Set i} → A → Set i
singleton {A = A} a = Σ A λ a' → a ≡ a'

singleton' : ∀ {i}{A : Set i} → A → Set i
singleton' {A = A} a = Σ A λ a' → a' ≡ a

J' : ∀ {i j}{X : Set i}{x : X}
   → (P : (y : X) → x ≡ y → Set j)
   → P x refl
   → (y : X)
   → (p : x ≡ y)
   → P y p
J' P u y refl = u

J : ∀ {i j}{X : Set i}
  → (P : (x y : X) → x ≡ y → Set j)
  → ((x : X) → P x x refl)
  → (x y : X)
  → (p : x ≡ y)
  → P x y p
J P u x y p = J' (P x) (u x) y p
