module sets.nat.ordering.lt.core where

open import sum
open import equality.core
open import function.isomorphism.core
open import sets.core
open import sets.nat.core
open import sets.nat.ordering.leq.core

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n
infixr 4 _<_

z<n : ∀ {n} → 0 < suc n
z<n = s≤s z≤n

<⇒≤ : ∀ {n m} → n < m → n ≤ m
<⇒≤ p = trans≤ suc≤ p

trans< : ∀ {n m p} → n < m → m < p → n < p
trans< p q = <⇒≤ (trans≤ (s≤s p) q)

ap<-suc : ∀ {n m} → n < m → suc n < suc m
ap<-suc = s≤s

compare : (n m : ℕ) → Ordering _<_ n m
compare zero zero = eq refl
compare zero (suc m) = lt z<n
compare (suc n) zero = gt z<n
compare (suc n) (suc m) with compare n m
... | lt p = lt (ap<-suc p)
... | eq p = eq (ap suc p)
... | gt p = gt (ap<-suc p)
