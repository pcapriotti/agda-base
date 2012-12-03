
{-# OPTIONS --without-K  #-}

module sets.nat where

open import level     using (lzero)
open import equality  using (_≡_; refl; cong)
open import function  using (_$_)
open import decidable using (Dec; yes; no)

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
