{-# OPTIONS --without-K #-}
module hott.level.sets.extra where

open import level
open import decidable
open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.extensionality.proof
open import sets.empty
open import sets.unit
open import hott.level.core

⊥-initial : ∀ {i j} {A : Set i} → contr (⊥ {j} → A)
⊥-initial = (λ ()) , (λ f → funext λ ())

-- Hedberg's theorem
hedberg : ∀ {i} {A : Set i}
        → ((x y : A) → Dec (x ≡ y))
        → h 2 A
hedberg {A = A} dec x y = prop⇒h1 ≡-prop
  where
    open ≡-Reasoning

    canonical : {x y : A} → x ≡ y → x ≡ y
    canonical {x} {y} p with dec x y
    ... | yes q = q
    ... | no _ = p

    canonical-const : {x y : A}
                    → (p q : x ≡ y)
                    → canonical p ≡ canonical q
    canonical-const {x} {y} p q with dec x y
    ... | yes _ = refl
    ... | no f = ⊥-elim (f p)

    canonical-inv : {x y : A}(p : x ≡ y)
                  → canonical p · sym (canonical refl) ≡ p
    canonical-inv refl = left-inverse (canonical refl)

    ≡-prop : {x y : A}(p q : x ≡ y) → p ≡ q
    ≡-prop p q = begin
        p
      ≡⟨ sym (canonical-inv p) ⟩
        canonical p · sym (canonical refl)
      ≡⟨ ap (λ z → z · sym (canonical refl))
              (canonical-const p q) ⟩
        canonical q · sym (canonical refl)
      ≡⟨ canonical-inv q ⟩
        q
      ∎

-- Bool is a set
private
  module BoolSet where
    open import sets.bool
    bool-set : h 2 Bool
    bool-set = hedberg _≟_
open BoolSet public

-- Nat is a set
private
  module NatSet where
    open import sets.nat.core
    nat-set : h 2 ℕ
    nat-set = hedberg _≟_
open NatSet public

-- Fin is a set
private
  module FinSet where
    open import sets.fin.core
    fin-set : ∀ n → h 2 (Fin n)
    fin-set n = hedberg _≟_
open FinSet public
