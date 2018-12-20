module sets.nat.ordering.leq.alternative where

open import equality.core
open import equality.calculus
open import function.isomorphism
open import hott.equivalence.logical
open import hott.level.core
open import hott.level.sets
open import sets.nat.core
open import sets.nat.properties
open import sets.nat.ordering.leq.core
open import sets.nat.ordering.leq.level
open import sum

Less : ℕ → ℕ → Set _
Less n m = Σ ℕ λ d → n + d ≡ m

Less-level : ∀ {n m} → h 1 (Less n m)
Less-level {n}{m} = prop⇒h1 λ { (d₁ , p₁) (d₂ , p₂)
  → unapΣ ( +-left-cancel n (p₁ · sym p₂)
          , h1⇒prop (nat-set _ _) _ _) }

leq-sum : ∀ {n m}(p : n ≤ m) → Less n m
leq-sum {m = m} z≤n = m , refl
leq-sum (s≤s p) with leq-sum p
leq-sum (s≤s p) | d , q = d , ap suc q

diff : ∀ {n m} → n ≤ m → ℕ
diff p = proj₁ (leq-sum p)

sum-leq : ∀ n d → n ≤ (n + d)
sum-leq n 0 = ≡⇒≤ (sym (+-right-unit _))
sum-leq n (suc d) = trans≤ (sum-leq n d)
                    (trans≤ suc≤ (≡⇒≤ ( ap suc (+-commutativity n d)
                                      · +-commutativity (suc d) n)))

leq-sum-iso : ∀ {n m} → (n ≤ m) ≅ Less n m
leq-sum-iso = ↔⇒≅ ≤-level Less-level
  ( leq-sum
  , (λ { (d , refl) → sum-leq _ d }))
