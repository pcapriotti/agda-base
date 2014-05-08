{-# OPTIONS --without-K #-}
module sets.vec.dependent where

open import sets.nat.core
open import sets.fin.core

-- syntactic sugar to create finite dependent functions

⟦⟧ : {P : Fin 0 → Set} → (i : Fin 0) → P i
⟦⟧ ()

_∷∷_ : ∀ {n}{P : Fin (suc n) → Set}
    → (x : P zero)(xs : (i : Fin n) → P (suc i))
    → (i : Fin (suc n)) → P i
_∷∷_ {P = P} x xs zero = x
_∷∷_ {P = P} x xs (suc i) = xs i

infixr 5 _∷∷_
