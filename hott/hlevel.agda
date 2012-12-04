{-# OPTIONS --without-K #-}
module hott.hlevel where

open import level using (_⊔_)
open import sum
open import sets.nat
open import equality using (_≡_ ; refl ; sym)
open import function using (_$_)
open import category.instances.discrete
open DiscreteGroupoid

-- h-levels
h : ∀ {i} → ℕ → Set i → Set i
h 0 X = Σ X λ x → (x' : X) → x ≡ x'
h (suc n) X = (x x' : X) →  h n (x ≡ x')

-- a set is contractible if it has one element and everything in the
-- set is equal to that (h₀)
contr : ∀ {i} → Set i → Set i
contr = h 0

-- a set is propositional if all elements are equal
isProp : ∀ {i} → Set i → Set i
isProp X = (x x' : X) → x ≡ x'

-- propositional and h1 are equivalent

-- (propositional says that all elements are equal and
--             h1 says that all elements are equal and
--                all equality proofs are equal)

h1⇒isProp : ∀ {i} (X : Set i) → h 1 X → isProp X
h1⇒isProp X h1 x x' = proj₁ $ h1 x x' 

isProp⇒h1 : ∀ {i} (X : Set i) → isProp X → h 1 X
isProp⇒h1 X f x y = p₀ x y , lem x y
  where
    p₀ : (x y : X) → x ≡ y
    p₀ x y = f x y ⊚ (f y y)⁻¹

    lem : (x y : X)(p : x ≡ y) → p₀ x y ≡ p
    lem x .x refl = left-inverse (f x x)

-- a contractible set is propositional
contr⇒isProp : ∀ {i} {X : Set i} → contr X → isProp X
contr⇒isProp (x , p) = λ x' x'' → sym (p x') ⊚ p x''

-- Prop: the set of propositions
Prop' : Set₁
Prop' = Σ Set isProp

-- the inverse image of a y ∈ Y considering a function f : X → Y
_⁻¹_ : ∀ {i k} {X : Set i} {Y : Set k} → (X → Y) → Y → Set (i ⊔ k)
f ⁻¹ y = Σ _ λ x → f x ≡ y