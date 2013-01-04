{-# OPTIONS --without-K  #-}

module sets.fin where

open import decidable
open import equality.core
open import sets.empty
open import sets.unit
open import sets.nat using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

private
  disj : ∀ {n}(i : Fin n) → ¬ (zero ≡ suc i)
  disj {n} i = J' P tt (suc i)
    where
      P : (i : Fin (suc n)) → zero ≡ i → Set
      P zero _ = ⊤
      P (suc _) _ = ⊥

  σ : ∀ {n} → Fin n → Fin (suc n)
  σ = suc

  suc-inj : ∀ {n} (i j : Fin n) → σ i ≡ σ j → i ≡ j
  suc-inj {n} i j = J' P refl (suc j)
    where
      P : (j : Fin (suc n)) → σ i ≡ j → Set
      P zero _ = ⊤
      P (suc j) _ = i ≡ j

_≟_ : ∀ {n} → (i j : Fin n) → Dec (i ≡ j)
_≟_ zero zero = yes refl
_≟_ zero (suc i) = no (disj i)
_≟_ (suc i) zero = no (λ p → disj i (sym p))
_≟_ {suc n} (suc i) (suc j) with i ≟ j
... | yes p = yes (cong suc p)
... | no a = no (λ p → a (suc-inj i j p))

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (suc i) = suc (toℕ i)
