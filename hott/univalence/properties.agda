{-# OPTIONS --without-K #-}
module hott.univalence.properties where

open import sum
open import equality.core
open import equality.calculus
open import function.extensionality
open import sets.nat using (suc)
open import hott.hlevel

import hott.univalence.properties.core as Core
open Core public
  hiding (exp-contr; Π-contr; Π-hlevel)

abstract
  Π-hlevel : ∀ {i j n} {X : Set i}{Y : X → Set j}
           → ((x : X) → h n (Y x))
           → h n ((x : X) → Y x)
  Π-hlevel = Core.Π-hlevel strong-ext

  -- being contractible is a proposition
  contr-h1 : ∀ {i}(X : Set i) → h 1 (contr X)
  contr-h1 X = prop⇒h1 λ { (x₀ , c₀) (x₁ , c₁) →
      uncongΣ (c₀ x₁ , contr⇒prop (lem (x₀ , c₀) x₁) _ _) }
    where
      lem : ∀ {i}{A : Set i} → contr A → (x : A) → contr ((x' : A) → x ≡ x')
      lem c x = Π-hlevel (λ x' → h↑ c x x')

  -- being of h-level n is a proposition
  hn-h1 : ∀ {i} n (X : Set i) → h 1 (h n X)
  hn-h1 0 X = contr-h1 X
  hn-h1 (suc n) X = Π-hlevel λ x → Π-hlevel λ y → hn-h1 n (x ≡ y)
