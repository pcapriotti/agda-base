{-# OPTIONS --without-K #-}
module sets.nat.core where

open import decidable
open import equality.core
open import function.core
open import function.isomorphism.core
open import sets.empty

infixr 8 _^_
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
0 * n = zero
suc m * n = n + m * n

_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (suc m) = n * (n ^ m)

suc-inj : injective suc
suc-inj = ap pred

_≟_ : (a b : ℕ) → Dec (a ≡ b)
zero  ≟ zero  = yes refl
zero  ≟ suc _ = no (λ ())
suc _ ≟ zero  = no (λ ())
suc a ≟ suc b with a ≟ b
suc a ≟ suc b | yes a≡b = yes $ ap suc a≡b
suc a ≟ suc b | no ¬a≡b = no $ (λ sa≡sb → ¬a≡b (ap pred sa≡sb))

