{-# OPTIONS --without-K #-}
module sets.nat.ordering.leq.core where

open import decidable
open import equality.core
open import function.core
open import sets.nat.core
open import sets.empty

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} (p : m ≤ n) → suc m ≤ suc n

ap-pred-≤ : ∀ {n m} → suc n ≤ suc m → n ≤ m
ap-pred-≤ (s≤s p) = p

refl≤ : {n : ℕ} → n ≤ n
refl≤ {0} = z≤n
refl≤ {suc n} = s≤s refl≤

≡⇒≤ : {n m : ℕ} → n ≡ m → n ≤ m
≡⇒≤ refl = refl≤

suc≤ : ∀ {n} → n ≤ suc n
suc≤ {0} = z≤n
suc≤ {suc n} = s≤s suc≤

suc≰ : ∀ {n} → ¬ (suc n ≤ n)
suc≰ {zero} ()
suc≰ {suc n} p = suc≰ (ap-pred-≤ p)

trans≤ : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
trans≤ z≤n q = z≤n
trans≤ (s≤s p) (s≤s q) = s≤s (trans≤ p q)

antisym≤ : ∀ {n m} → n ≤ m → m ≤ n → n ≡ m
antisym≤ z≤n z≤n = refl
antisym≤ (s≤s p) (s≤s q) = ap suc (antisym≤ p q)
