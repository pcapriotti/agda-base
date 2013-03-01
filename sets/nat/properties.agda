{-# OPTIONS --without-K #-}

module sets.nat.properties where

open import equality.core
open import equality.calculus
open import equality.reasoning
open import sets.nat.core

+-left-unit : ∀ n → 0 + n ≡ n
+-left-unit n = refl

+-right-unit : ∀ n → n + 0 ≡ n
+-right-unit zero = refl
+-right-unit (suc n) = cong suc (+-right-unit n)

+-associativity : ∀ n m p → n + m + p ≡ n + (m + p)
+-associativity 0 m p = refl
+-associativity (suc n) m p = cong suc (+-associativity n m p)

right-distr : ∀ n m p → (n + m) * p ≡ n * p + m * p
right-distr 0 m p = refl
right-distr (suc n) m p = begin
    p + (n + m) * p
  ≡⟨ cong (_+_ p) (right-distr n m p) ⟩
    p + (n * p + m * p)
  ≡⟨ sym (+-associativity p (n * p) (m * p)) ⟩
    p + n * p + m * p
  ∎
  where open ≡-Reasoning

*-left-unit : ∀ n → 1 * n ≡ n
*-left-unit n = +-right-unit n

*-right-unit : ∀ n → n * 1 ≡ n
*-right-unit zero = refl
*-right-unit (suc n) = cong suc (*-right-unit n)

*-associativity : ∀ n m p → n * m * p ≡ n * (m * p)
*-associativity 0 m p = refl
*-associativity (suc n) m p =
    right-distr m (n * m) p
  ⊚ cong (λ z → (m * p) + z)
         (*-associativity n m p)

+-commutativity : ∀ n m → n + m ≡ m + n
+-commutativity 0 m = sym (+-right-unit m)
+-commutativity (suc n) m = begin
    suc (n + m)
  ≡⟨ cong suc (+-commutativity n m) ⟩
    suc (m + n)
  ≡⟨ lem m n ⟩
    m + suc n
  ∎
  where
    open ≡-Reasoning
    lem : ∀ n m → suc n + m ≡ n + suc m
    lem 0 m = refl
    lem (suc n) m = cong suc (lem n m)

left-distr : ∀ n m p → n * (m + p) ≡ n * m + n * p
left-distr 0 m p = refl
left-distr (suc n) m p = begin
    m + p + n * (m + p)
  ≡⟨ +-associativity m p _ ⟩
    m + (p + n * (m + p))
  ≡⟨ cong (λ z → m + (p + z))
          (left-distr n m p) ⟩
    m + (p + (n * m + n * p))
  ≡⟨ cong (_+_ m)
          (sym (+-associativity p (n * m) _)) ⟩
    m + (p + n * m + n * p)
  ≡⟨ cong (λ z → m + (z + n * p))
          (+-commutativity p (n * m)) ⟩
    m + (n * m + p + n * p)
  ≡⟨ cong (_+_ m) (+-associativity (n * m) p _) ⟩
    m + (n * m + (p + n * p))
  ≡⟨ sym (+-associativity m (n * m) _) ⟩
    m + n * m + (p + n * p)
  ∎
  where open ≡-Reasoning

left-zero : ∀ n → 0 * n ≡ 0
left-zero n = refl

right-zero : ∀ n → n * 0 ≡ 0
right-zero 0 = refl
right-zero (suc n) = right-zero n

*-commutativity : ∀ n m → n * m ≡ m * n
*-commutativity 0 m = sym (right-zero m)
*-commutativity (suc n) m = begin
    m + n * m
  ≡⟨ cong₂ _+_ (sym (*-right-unit m))
               (*-commutativity n m) ⟩
    m * 1 + m * n
  ≡⟨ sym (left-distr m 1 n) ⟩
    m * suc n
  ∎
  where open ≡-Reasoning
