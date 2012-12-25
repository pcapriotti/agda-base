{-# OPTIONS --without-K #-}
module equality.solver.example where

open import sum
open import equality.core
open import equality.calculus
open import sets.fin using (Fin; zero; suc; _≟_)
open import sets.vec

open import equality.solver
open import equality.solver.core
open import equality.solver.builder
open import equality.solver.term
  hiding (module WithEnv)

open WithDec
open WithEnv

example : {X : Set}{x y z w : X}
        → (p : x ≡ y)
        → (q : y ≡ z)
        → (r : z ≡ w)
        → p ⊚ q ⊚ r ⊚ sym r ⊚ sym q ⊚ sym p ≡ refl
example {X}{x}{y}{z}{w} p q r = solve X (fin-graph (Fin 4) v) (fin-graph-dec (Fin 4) v _≟_) env t₁ t₂ refl
  where
    v : Vec (Fin 4 × Fin 4) 3
    v = (zero , suc zero)
      ∷ (suc zero , suc (suc zero))
      ∷ (suc (suc zero) , suc (suc (suc zero)))
      ∷ []

    t₁ : Term (fin-graph (Fin 4) v) zero zero
    t₁ = term (λ {W} a b c → a * b * c * inv c * inv b * inv a)

    t₂ : Term (fin-graph (Fin 4) v) zero zero
    t₂ = term (λ {W} _ _ _ → null)

    env : Env (fin-graph (Fin 4) v) X
    env = record
      { imap = g
      ; gmap = f }
      where
        g : Fin 4 → X
        g = lookup (x ∷ y ∷ z ∷ w ∷ [])

        f : ∀ {i j} → fin-graph (Fin 4) v i j → g i ≡ g j
        f (fin-element zero) = p
        f (fin-element (suc zero)) = q
        f (fin-element (suc (suc zero))) = r
        f (fin-element (suc (suc (suc ()))))
