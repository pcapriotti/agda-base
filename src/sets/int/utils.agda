{-# OPTIONS --without-K #-}

module sets.int.utils where

open import sum
open import equality
open import function
open import sets.nat.core
open import sets.int.definition
open import hott.level

module _ {i}{X : Set i}(hX : h 2 X)
  (f : ℕ → ℕ → ℕ → ℕ → X)
  (u : ∀ n n' d m m' e → f n n' m m' ≡ f (d + n) (d + n') (e + m) (e + m')) where

  private
    g : ℕ → ℕ → ℤ → X
    g n n' = elim-ℤ hX (f n n' , u n n' 0)

    lem : (n n' d m m' : ℕ) → g n n' (m [-] m') ≡ g (d + n) (d + n') (m [-] m')
    lem n n' d m m' = u n n' d m m' 0

    v : (n n' d : ℕ) → g n n' ≡ g (d + n) (d + n')
    v n n' d = funext λ m → elim-prop-ℤ
      (λ m → hX (g n n' m) (g (d + n) (d + n') m))
      (lem n n' d) m

    hX' : h 2 (ℤ → X)
    hX' = Π-level λ _ → hX

  elim₂-ℤ : ℤ → ℤ → X
  elim₂-ℤ = elim-ℤ hX' (g , v)

elim₂-prop-ℤ : ∀ {i}{X : ℤ → ℤ → Set i} → (∀ n m → h 1 (X n m))
             → ((n n' m m' : ℕ) → X (n [-] n') (m [-] m'))
             → ∀ n m → X n m
elim₂-prop-ℤ {i}{X} hX f = elim-prop-ℤ hX' g
  where
    g : (n n' : ℕ) → ∀ m → X (n [-] n') m
    g n n' = elim-prop-ℤ (hX (n [-] n')) (f n n')

    hX' : ∀ n → h 1 (∀ m → X n m)
    hX' n = Π-level λ m → hX n m

elim₃-prop-ℤ : ∀ {i}{X : ℤ → ℤ → ℤ → Set i} → (∀ n m p → h 1 (X n m p))
             → ((n n' m m' p p' : ℕ) → X (n [-] n') (m [-] m') (p [-] p'))
             → ∀ n m p → X n m p
elim₃-prop-ℤ {i}{X} hX f = elim-prop-ℤ hX' g
  where
    g : (n n' : ℕ) → ∀ m p → X (n [-] n') m p
    g n n' = elim₂-prop-ℤ (hX (n [-] n')) (f n n')

    hX' : ∀ n → h 1 (∀ m p → X n m p)
    hX' n = Π-level λ m → Π-level λ p → hX n m p
