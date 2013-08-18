{-# OPTIONS --without-K #-}
module sets.nat.ordering where

open import sum
open import equality.core
open import function.isomorphism.core
open import sets.nat.core

data _<_ : ℕ → ℕ → Set where
  suc< : ∀ {n} → n < suc n
  n<s : ∀ {m n} → n < m → n < suc m
infixr 4 _<_

z<n : ∀ {n} → 0 < suc n
z<n {zero} = suc<
z<n {suc n} = n<s z<n

trans< : ∀ {n m p} → n < m → m < p → n < p
trans< a suc< = n<s a
trans< a (n<s b) = n<s (trans< a b)

ap<-suc : ∀ {n m} → n < m → suc n < suc m
ap<-suc suc< = suc<
ap<-suc (n<s p) = n<s (ap<-suc p)

data Ordering (n m : ℕ) : Set where
  lt : n < m → Ordering n m
  eq : n ≡ m → Ordering n m
  gt : m < n → Ordering n m

compare : (n m : ℕ) → Ordering n m
compare zero zero = eq refl
compare zero (suc m) = lt z<n
compare (suc n) zero = gt z<n
compare (suc n) (suc m) with compare n m
... | lt p = lt (ap<-suc p)
... | eq p = eq (ap suc p)
... | gt p = gt (ap<-suc p)
