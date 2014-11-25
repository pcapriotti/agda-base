{-# OPTIONS --without-K #-}
module sets.nat.struct where

open import equality
open import function.extensionality
open import function.isomorphism.core
open import container.core
open import container.w
open import sets.unit
open import sets.nat.core
open import sets.fin
open import sets.vec.dependent

ℕ-c : Container _ _ _
ℕ-c = record
  { I = ⊤
  ; A = λ _ → Fin 2
  ; B = Fin 0 ∷∷ Fin 1 ∷∷ ⟦⟧
  ; r = λ _ → tt }

ℕ-struct-iso : ℕ ≅ W ℕ-c tt
ℕ-struct-iso = iso f g α β
  where
    f : ℕ → W ℕ-c tt
    f 0 = sup (# 0) (λ ())
    f (suc n) = sup (# 1) (λ _ → f n)

    g : W ℕ-c tt → ℕ
    g (sup zero u) = 0
    g (sup (suc zero) u) = suc (g (u (# 0)))
    g (sup (suc (suc ())) u)

    α : (n : ℕ) → g (f n) ≡ n
    α zero = refl
    α (suc n) = ap suc (α n)

    β : (n : W ℕ-c tt) → f (g n) ≡ n
    β (sup zero u) = ap (sup zero) (funext λ ())
    β (sup (suc zero) u) = ap (sup (# 1)) (funext (β (u zero) ∷∷ ⟦⟧))
    β (sup (suc (suc ())) u)
