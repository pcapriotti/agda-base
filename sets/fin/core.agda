module sets.fin.core where

open import decidable
open import equality.core
open import sets.empty
open import sets.unit public
open import sets.nat.core
  hiding (_≟_; pred)
open import sets.empty

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

raise : ∀ {n} → Fin n → Fin (suc n)
raise zero = zero
raise (suc i) = suc (raise i)

fin-disj : ∀ {n}(i : Fin n) → ¬ (zero ≡ suc i)
fin-disj {n} i = J' P tt (suc i)
  where
    P : (i : Fin (suc n)) → zero ≡ i → Set
    P zero _ = ⊤
    P (suc _) _ = ⊥

fin-suc-inj : ∀ {n} {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
fin-suc-inj {n}{i}{j} = J' P refl (suc j)
  where
    P : (j : Fin (suc n)) → Fin.suc i ≡ j → Set
    P zero _ = ⊤
    P (suc j) _ = i ≡ j

_≟_ : ∀ {n} → (i j : Fin n) → Dec (i ≡ j)
_≟_ zero zero = yes refl
_≟_ zero (suc i) = no (fin-disj i)
_≟_ (suc i) zero = no (λ p → fin-disj i (sym p))
_≟_ {suc n} (suc i) (suc j) with i ≟ j
... | yes p = yes (ap suc p)
... | no a = no (λ p → a (fin-suc-inj p))

last-fin : {n : ℕ} → Fin (suc n)
last-fin {zero} = zero
last-fin {suc n} = suc last-fin
