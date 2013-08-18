{-# OPTIONS --without-K #-}
module hott.hlevel.core where

open import level using (_⊔_; lsuc)
open import sum
open import sets.nat.core
open import equality.core
open import equality.groupoid
open import function.core using (_$_)

-- h-levels
h : ∀ {i} → ℕ → Set i → Set i
h 0 X = Σ X λ x → (x' : X) → x ≡ x'
h (suc n) X = (x x' : X) →  h n (x ≡ x')

-- a set is contractible if it has one element and everything in the
-- set is equal to that (h₀)
contr : ∀ {i} → Set i → Set i
contr = h 0

-- a set is propositional if all elements are equal
prop : ∀ {i} → Set i → Set i
prop X = (x x' : X) → x ≡ x'

-- propositional and h1 are equivalent

-- (propositional says that all elements are equal and
--             h1 says that all elements are equal and
--                all equality proofs are equal)

h1⇒prop : ∀ {i} {X : Set i} → h 1 X → prop X
h1⇒prop h1 x x' = proj₁ $ h1 x x' 

prop⇒h1 : ∀ {i} {X : Set i} → prop X → h 1 X
prop⇒h1 {X = X} f x y = p₀ x y , lem x y
  where
    p₀ : (x y : X) → x ≡ y
    p₀ x y = f x y · (f y y)⁻¹

    lem : (x y : X)(p : x ≡ y) → p₀ x y ≡ p
    lem x .x refl = left-inverse (f x x)

-- a contractible set is propositional
contr⇒prop : ∀ {i} {X : Set i} → contr X → prop X
contr⇒prop (x , p) = λ x' x'' → sym (p x') · p x''

-- h-levels are upwards closed
h↑ : ∀ {i n}{X : Set i} → h n X → h (suc n) X
h↑ {n = 0} c = prop⇒h1 (contr⇒prop c)
h↑ {n = suc n} hn = λ x x' → h↑ (hn x x')

-- Prop: the set of propositions
HProp : ∀ i → Set (lsuc i)
HProp i = Σ (Set i) (h 1)

-- HSet : sets
HSet : ∀ i → Set (lsuc i)
HSet i = Σ (Set i) (h 2)

-- Types by h-level (shifted by 2)
Type : ∀ i → ℕ → Set (lsuc i)
Type i n = Σ (Set i) (h (suc (suc n)))

-- the inverse image of a y ∈ Y considering a function f : X → Y
_⁻¹_ : ∀ {i k} {X : Set i} {Y : Set k} → (X → Y) → Y → Set (i ⊔ k)
f ⁻¹ y = Σ _ λ x → f x ≡ y

-- singletons are contractible
singl-contr : ∀ {i} {A : Set i} → (x : A) → contr (singleton x)
singl-contr {A = A} x = (x , refl) , λ { (x' , p) → lem x' p }
  where
    lem : (x' : A)(p : x ≡ x') → (x , refl) ≡ (x' , p)
    lem .x refl = refl

singl-contr' : ∀ {i} {A : Set i} → (x : A) → contr (singleton' x)
singl-contr' {A = A} x = (x , refl) , λ { (x' , p) → lem x' p }
  where
    lem : (x' : A)(p : x' ≡ x) → (x , refl) ≡ (x' , p)
    lem .x refl = refl
