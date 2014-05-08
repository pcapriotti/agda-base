{-# OPTIONS --without-K #-}
module sets.fin.ordering where

open import equality.core
open import function.isomorphism
open import sets.core
open import sets.fin.core
open import sets.fin.properties
import sets.nat.ordering as N

_<_ : ∀ {n} → Fin n → Fin n → Set
i < j = toℕ i N.< toℕ j
infixr 4 _<_

ord-from-ℕ : ∀ {n} {i j : Fin n}
           → Ordering N._<_ (toℕ i) (toℕ j)
           → Ordering _<_ i j
ord-from-ℕ (lt p) = lt p
ord-from-ℕ (eq p) = eq (toℕ-inj p)
ord-from-ℕ (gt p) = gt p

compare : ∀ {n} → (i j : Fin n) → Ordering _<_ i j
compare i j = ord-from-ℕ (N.compare (toℕ i) (toℕ j))
