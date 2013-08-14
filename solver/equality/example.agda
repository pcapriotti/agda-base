{-# OPTIONS --without-K #-}
module solver.equality.example where

open import sum
open import equality.core
open import equality.calculus
open import sets.fin
open import sets.vec

open import solver.equality

example : {X : Set}{x y z w : X}
        → (p : x ≡ y)
        → (q : y ≡ z)
        → (r : z ≡ w)
        → p · q · r · sym r · sym q · sym p
        ≡ p · sym p
example {X}{x}{y}{z}{w} p q r = solve
  -- points
  (x ∷ y ∷ z ∷ w ∷ [])
  -- types of paths
  ((# 0 , # 1) ∷ (# 1 , # 2) ∷ (# 2 , # 3) ∷ [])
  -- paths
  (p ∷∷ q ∷∷ r ∷∷ ⟦⟧)
  -- first term
  (λ p q r → p * q * r * inv r * inv q * inv p)
  -- second term
  (λ p _ _ → p * inv p)
  -- always pass refl here
  refl
