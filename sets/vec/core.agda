{-# OPTIONS --type-in-type --without-K #-}
module sets.vec.core where

open import function.core
open import sets.nat.core using (ℕ; zero; suc)
open import sets.fin

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
infixr 5 _∷_

tabulate : {A : Set}{n : ℕ}
         → (Fin n → A) → Vec A n
tabulate {n = zero} _ = []
tabulate {n = suc m} f = f zero ∷ tabulate (f ∘ suc)

lookup : {A : Set}{n : ℕ}
       → Vec A n → Fin n → A
lookup [] ()
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

_!_ : {A : Set}{n : ℕ}
    → Vec A n → Fin n → A
_!_ = lookup
