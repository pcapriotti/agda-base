{-# OPTIONS --without-K #-}
module equality.groupoid where

open import category.groupoid using (Groupoid)
open import equality.core
open import level using (lzero)
open import function using (id)

equality-groupoid : ∀ {i} (A : Set i) → Groupoid i i
equality-groupoid A = record
  { cat = record
    { obj = A
    ; hom = _≡_
    ; id = λ x → refl {x = x}
    ; _∘_ = λ p q → trans q p
    ; left-unit = left-unit
    ; right-unit = right-unit
    ; associativity = associativity }
  ; sym = sym
  ; left-inverse = left-inverse
  ; right-inverse = right-inverse }
  where
    open import equality.properties

cong : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {i j} {A : Set i}{x y : A}
      → (B : A → Set j) → x ≡ y
      → B x → B y
subst B refl = id

module Exports {i}{A : Set i} where
  open import category.category
  open import category.groupoid

  open Groupoid (equality-groupoid A) public
    hiding (sym ; id ; _∘_)
open Exports public
