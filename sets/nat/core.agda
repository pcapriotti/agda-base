{-# OPTIONS --without-K #-}
module sets.nat.core where

open import level
open import equality.core
open import function.core
open import decidable

infixl 7 _*_
infixl 6 _+_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

_≟_ : (a b : ℕ) → Dec (a ≡ b)
zero  ≟ zero  = yes refl
zero  ≟ suc _ = no (λ ())
suc _ ≟ zero  = no (λ ())
suc a ≟ suc b with a ≟ b
suc a ≟ suc b | yes a≡b = yes $ ap suc a≡b
suc a ≟ suc b | no ¬a≡b = no $ (λ sa≡sb → ¬a≡b (ap pred sa≡sb))

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} (p : m ≤ n) → suc m ≤ suc n

ap-pred-≤ : ∀ {n m} → suc n ≤ suc m → n ≤ m
ap-pred-≤ (s≤s p) = p

refl-≤ : {n : ℕ} → n ≤ n
refl-≤ {0} = z≤n
refl-≤ {suc n} = s≤s refl-≤

_≤?_ : (n m : ℕ) → Dec (n ≤ m)
0 ≤? n = yes z≤n
suc _ ≤? 0 = no (λ ())
suc n ≤? suc m with n ≤? m
... | yes p = yes (s≤s p)
... | no f = no (f ∘ ap-pred-≤)
