{-# OPTIONS --without-K #-}

module sets.int.properties where

open import equality
open import function.core
import sets.nat as N
open N using (ℕ; suc)
open import sets.int.definition
open import sets.int.utils
import sets.int.core as Z

private
  module _ where
    open N

    add-right-unit : ∀ n n' → (n + 0) [-] (n' + 0) ≡ n [-] n'
    add-right-unit n n' = ap₂ _[-]_ (+-right-unit n) (+-right-unit n')

    add-left-inverse : ∀ n n' → (n' + n) [-] (n + n') ≡ 0 [-] 0
    add-left-inverse n n' = sym
      $ eq-ℤ 0 0 (n' + n)
      · ap₂ _[-]_ (+-right-unit (n' + n))
                  (+-right-unit (n' + n) · +-commutativity n' n)

module _ where
  open Z

  +-left-unit : ∀ n → zero + n ≡ n
  +-left-unit = elim-prop-ℤ (λ n → hℤ (zero + n) n)
                            (λ n n' → refl)

  +-right-unit : ∀ n → n + zero ≡ n
  +-right-unit = elim-prop-ℤ (λ n → hℤ (n + zero) n)
                             add-right-unit

  +-left-inverse : ∀ n → negate n + n ≡ zero
  +-left-inverse = elim-prop-ℤ (λ n → hℤ (negate n + n) zero)
                               add-left-inverse

  +-right-inverse : ∀ n → n + negate n ≡ zero
  +-right-inverse = elim-prop-ℤ (λ n → hℤ (n + negate n) zero)
                                (λ n n' → add-left-inverse n' n)

  inc-dec : ∀ n → inc (dec n) ≡ n
  inc-dec = elim-prop-ℤ (λ n → hℤ (inc (dec n)) n)
                        (λ n n' → sym (eq-ℤ n n' 1))

  dec-inc : ∀ n → dec (inc n) ≡ n
  dec-inc = elim-prop-ℤ (λ n → hℤ (dec (inc n)) n)
                        (λ n n' → sym (eq-ℤ n n' 1))

  +-associativity : ∀ n m p → n + m + p ≡ n + (m + p)
  +-associativity = elim₃-prop-ℤ
    (λ n m p → hℤ (n + m + p) (n + (m + p)))
    (λ n n' m m' p p' → ap₂ _[-]_ (N.+-associativity n m p)
                                  (N.+-associativity n' m' p'))
