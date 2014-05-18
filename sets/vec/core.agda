{-# OPTIONS --without-K #-}
module sets.vec.core where

open import function.core
open import sets.nat.core using (ℕ; zero; suc)
open import sets.fin

data Vec {i}(A : Set i) : ℕ → Set i where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
infixr 5 _∷_

head : ∀ {i}{A : Set i}{n : ℕ} → Vec A (suc n) → A
head (x ∷ _) = x

tail : ∀ {i}{A : Set i}{n : ℕ} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

tabulate : ∀ {i}{A : Set i}{n : ℕ}
         → (Fin n → A) → Vec A n
tabulate {n = zero} _ = []
tabulate {n = suc m} f = f zero ∷ tabulate (f ∘ suc)

lookup : ∀ {i}{A : Set i}{n : ℕ}
       → Vec A n → Fin n → A
lookup [] ()
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

_!_ : ∀ {i}{A : Set i}{n : ℕ}
    → Vec A n → Fin n → A
_!_ = lookup
