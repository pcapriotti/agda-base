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

Π-hlevel : ∀ {i j n} {X : Set i}{Y : X → Set j}
         → ((x : X) → h n (Y x))
         → h n ((x : X) → Y x)
Π-hlevel = Core.Π-hlevel strong-ext

-- being contractible is a proposition
contr-prop : ∀ {i}(X : Set i) → prop (contr X)
contr-prop X (x₀ , c₀) (x₁ , c₁) =
    uncongΣ (c₀ x₁ , contr⇒prop (lem (x₀ , c₀) x₁) _ _)
  where
    lem : ∀ {i}{A : Set i} → contr A → (x : A) → contr ((x' : A) → x ≡ x')
    lem c x = Π-hlevel (λ x' → h↑ c x x')

-- being of h-level n is a proposition
hn-prop : ∀ {i} n (X : Set i) → prop (h n X)
hn-prop n X = h1⇒prop (lem n X)
  where
    lem : ∀ {i} n (X : Set i) → h 1 (h n X)
    lem 0 X = prop⇒h1 (contr-prop X)
    lem (suc n) X = Π-hlevel λ x → Π-hlevel λ y → lem n (x ≡ y)
