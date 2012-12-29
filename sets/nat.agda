
{-# OPTIONS --without-K  #-}

module sets.nat where

open import level
  using (lzero)
open import equality.core
  using (_≡_; refl; cong)
open import function
  using (_$_; _∘_)
open import decidable
  using (Dec; yes; no)

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
suc a ≟ suc b | yes a≡b = yes $ cong {lzero} {lzero} suc a≡b
suc a ≟ suc b | no ¬a≡b = no $ (λ sa≡sb → ¬a≡b (cong {lzero} {lzero} pred sa≡sb))

data _≤_ : ℕ → ℕ → Set where
  refl-≤ : ∀ n → n ≤ n
  suc-≤ : ∀ {n m} → n ≤ m → n ≤ suc m

zero-min : ∀ n → 0 ≤ n
zero-min 0 = refl-≤ 0
zero-min (suc n) = suc-≤ (zero-min n)

cong-suc-≤ : ∀ {n m} → n ≤ m → suc n ≤ suc m
cong-suc-≤ (refl-≤ n) = refl-≤ (suc n)
cong-suc-≤ (suc-≤ p) = suc-≤ (cong-suc-≤ p)

cong-pred-≤ : ∀ {n m} → suc n ≤ suc m → n ≤ m
cong-pred-≤ {n} (refl-≤ .(suc n)) = refl-≤ n
cong-pred-≤ {n}{0} (suc-≤ ())
cong-pred-≤ {n}{suc m} (suc-≤ p) = suc-≤ (cong-pred-≤ p)

_≤?_ : (n m : ℕ) → Dec (n ≤ m)
0 ≤? n = yes (zero-min n)
suc _ ≤? 0 = no (λ ())
suc n ≤? suc m with n ≤? m
... | yes p = yes (cong-suc-≤ p)
... | no f = no (f ∘ cong-pred-≤)
