{-# OPTIONS --without-K #-}

module sets.int.core where

open import sum
open import equality
open import function
import sets.nat as N
open N using (ℕ; suc)
open import sets.int.definition
open import sets.int.utils
open import sets.vec
open import hott.hlevel.closure

infixl 7 _*_
infixl 6 _+_

from-nat : ℕ → ℤ
from-nat n = n [-] 0

zero : ℤ
zero = from-nat 0

one : ℤ
one = from-nat 1

private
  module _ where
    open N

    add : ℕ → ℕ → ℕ → ℕ → ℤ
    add n n' m m' = (n + m) [-] (n' + m')

    add-sound : (n n' d m m' e : ℕ)
              → add n n' m m'
              ≡ add (d + n) (d + n') (e + m) (e + m')
    add-sound n n' d m m' e
      = eq-ℤ (n + m) (n' + m') (d + e)
      · ap₂ _[-]_ (solve 4 (exp λ d e n m → d :+ e :+ (n :+ m))
                           (exp λ d e n m → d :+ n :+ (e :+ m))
                           (d ∷∷ e ∷∷ n ∷∷ m ∷∷ ⟦⟧))
                  (solve 4 (exp λ d e n m → d :+ e :+ (n :+ m))
                           (exp λ d e n m → d :+ n :+ (e :+ m))
                           (d ∷∷ e ∷∷ n' ∷∷ m' ∷∷ ⟦⟧))

    mul : ℕ → ℕ → ℕ → ℕ → ℤ
    mul n n' m m' = (n * m + n' * m') [-] (n' * m + n * m')

    mul-sound : (n n' d m m' e : ℕ)
              → mul n n' m m'
              ≡ mul (d + n) (d + n') (e + m) (e + m')
    mul-sound n n' d m m' e
      = eq-ℤ (n * m + n' * m') (n' * m + n * m')
             (d * e + d * m + n * e + d * e + d * m' + n' * e)
      · ap₂ _[-]_ lem₁ lem₂
      where
        distr₂ : ∀ a b c d
               → (a + b) * (c + d)
               ≡ a * c + a * d + b * c + b * d
        distr₂ a b c d = right-distr a b (c + d)
                       · ap₂ _+_ (left-distr a c d) (left-distr b c d)
                       · sym (+-associativity (a * c + a * d) (b * c) (b * d))

        lem₁ : d * e + d * m + n * e + d * e + d * m' + n' * e + (n * m + n' * m')
             ≡ (d + n) * (e + m) + (d + n') * (e + m')
        lem₁ = sym
             $ ap₂ _+_ (distr₂ d n e m) (distr₂ d n' e m')
             · solve 7 (exp λ a b c d e f g → a :+ b :+ c :+ d :+ (a :+ e :+ f :+ g))
                       (exp λ a b c d e f g → a :+ b :+ c :+ a :+ e :+ f :+ (d :+ g))
                       ((d * e) ∷∷ (d * m) ∷∷ (n * e) ∷∷ (n * m) ∷∷
                        (d * m') ∷∷ (n' * e) ∷∷ (n' * m') ∷∷ ⟦⟧)

        lem₂ : d * e + d * m + n * e + d * e + d * m' + n' * e + (n' * m + n * m')
             ≡ (d + n') * (e + m) + (d + n) * (e + m')
        lem₂ = sym
             $ ap₂ _+_ (distr₂ d n' e m) (distr₂ d n e m')
             · solve 7 (exp λ a b c d e f g → a :+ b :+ c :+ d :+ (a :+ e :+ f :+ g))
                         (exp λ a b c d e f g → a :+ b :+ f :+ a :+ e :+ c :+ (d :+ g))
                         ((d * e) ∷∷ (d * m) ∷∷ (n' * e) ∷∷ (n' * m) ∷∷
                          (d * m') ∷∷ (n * e) ∷∷ (n * m') ∷∷ ⟦⟧)

    neg : ℕ → ℕ → ℤ
    neg n n' = n' [-] n

    neg-sound : (n n' d : ℕ) → neg n n' ≡ neg (d + n) (d + n')
    neg-sound n n' d = eq-ℤ n' n d

_+_ : ℤ → ℤ → ℤ
_+_ = elim₂-ℤ hℤ add add-sound

negate : ℤ → ℤ
negate = elim-ℤ hℤ (neg , neg-sound)

inc : ℤ → ℤ
inc n = one + n

dec : ℤ → ℤ
dec n = negate one + n

_*_ : ℤ → ℤ → ℤ
_*_ = elim₂-ℤ hℤ mul mul-sound
