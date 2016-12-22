{-# OPTIONS --without-K #-}
module sets.finite.core where

open import sum
open import function.isomorphism
open import sets.nat
open import sets.fin

IsOfSize : ∀ {i} → Set i → ℕ → Set i
IsOfSize A n = A ≅ Fin n

IsFinite : ∀ {i} → Set i → Set i
IsFinite A = Σ ℕ (IsOfSize A)

mk-is-finite : ∀ {i n}{A : Set i}
             → (A ≅ Fin n)
             → IsFinite A
mk-is-finite {n = n} enum = n , enum

fin-is-finite : ∀ {n} → IsFinite (Fin n)
fin-is-finite {n} = mk-is-finite refl≅

⊎-of-size : ∀ {i j n m}{A : Set i}{B : Set j}
          → IsOfSize A n
          → IsOfSize B m
          → IsOfSize (A ⊎ B) (n + m)
⊎-of-size isoA isoB = ⊎-ap-iso isoA isoB ·≅ fin-sum

⊎-finite : ∀ {i j}{A : Set i}{B : Set j}
         → IsFinite A → IsFinite B
         → IsFinite (A ⊎ B)
⊎-finite (_ , fA) (_ , fB) = mk-is-finite (⊎-of-size fA fB)

×-of-size : ∀ {i j n m}{A : Set i}{B : Set j}
          → IsOfSize A n
          → IsOfSize B m
          → IsOfSize (A × B) (n * m)
×-of-size isoA isoB = ×-ap-iso isoA isoB ·≅ fin-prod

×-finite : ∀ {i j}{A : Set i}{B : Set j}
         → IsFinite A → IsFinite B
         → IsFinite (A × B)
×-finite (_ , fA) (_ , fB) = mk-is-finite (×-of-size fA fB)
