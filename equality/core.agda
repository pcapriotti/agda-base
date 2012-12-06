{-# OPTIONS --without-K #-}
module equality.core where

open import sum
open import level using ()
open import function using (id)

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

sym : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {i} {A : Set i} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

cong : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {i j} {A : Set i}{x y : A}
      → (B : A → Set j) → x ≡ y
      → B x → B y
subst B refl = id

singleton : ∀ {i}{A : Set i} → A → Set i
singleton {A = A} a = Σ A λ a' → a ≡ a'