{-# OPTIONS --without-K #-}
module sets.finite.core where

open import sum
open import function.isomorphism
open import sets.nat
open import sets.fin

IsOfSize : Set → ℕ → Set
IsOfSize A n = A ≅ Fin n

IsFinite : Set → Set
IsFinite A = Σ ℕ (IsOfSize A)

mk-is-finite : ∀ {n}{A : Set}
             → (A ≅ Fin n)
             → IsFinite A
mk-is-finite {n = n} enum = n , enum

fin-is-finite : ∀ {n} → IsFinite (Fin n)
fin-is-finite {n} = mk-is-finite refl≅

⊎-of-size : ∀ {n m}{A : Set}{B : Set}
          → IsOfSize A n
          → IsOfSize B m
          → IsOfSize (A ⊎ B) (n + m)
⊎-of-size isoA isoB = ⊎-ap-iso isoA isoB ·≅ fin-sum

⊎-finite : {A : Set}{B : Set}
         → IsFinite A → IsFinite B
         → IsFinite (A ⊎ B)
⊎-finite (_ , fA) (_ , fB) = mk-is-finite (⊎-of-size fA fB)

×-of-size : ∀ {n m}{A : Set}{B : Set}
          → IsOfSize A n
          → IsOfSize B m
          → IsOfSize (A × B) (n * m)
×-of-size isoA isoB = ×-ap-iso isoA isoB ·≅ fin-prod

×-finite : {A : Set}{B : Set}
         → IsFinite A → IsFinite B
         → IsFinite (A × B)
×-finite (_ , fA) (_ , fB) = mk-is-finite (×-of-size fA fB)
