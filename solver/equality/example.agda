{-# OPTIONS --without-K #-}
module solver.equality.example where

open import sum
open import equality.core
open import equality.calculus
open import sets.fin
open import sets.vec

open import solver.equality
open import solver.equality.core
open import solver.equality.builder
open import solver.equality.term
  hiding (module WithEnv)

open WithDec
open WithEnv

example : {X : Set}{x y z w : X}
        → (p : x ≡ y)
        → (q : y ≡ z)
        → (r : z ≡ w)
        → p ⊚ q ⊚ r ⊚ sym r ⊚ sym q ⊚ sym p ≡ refl
example {X}{x}{y}{z}{w} p q r = solve X (fin-graph (Fin 4) v)
                                        (fin-graph-dec (Fin 4) v _≟_)
                                        env t₁ t₂ refl
  where
    v = (# 0 , # 1) ∷ (# 1 , # 2) ∷ (# 2 , # 3) ∷ []
    t₁ = term (λ a b c → a * b * c * inv c * inv b * inv a)
    t₂ = term (λ _ _ _ → null)
    env = fin-env v (x ∷ y ∷ z ∷ w ∷ []) (p ∷∷ q ∷∷ r ∷∷ ⟦⟧)
