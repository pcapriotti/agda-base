{-# OPTIONS --without-K #-}
module solver.equality where

open import sum
open import equality.core
open import sets.fin
open import sets.nat using (ℕ)
open import sets.vec
open import solver.equality.core
open import solver.equality.solver
open import solver.equality.builder
open import solver.equality.term public
  hiding (module WithEnv)

private
  module Solver {ll} {X : Set ll}{k n : ℕ}
                (xs : Vec X k){x y : Fin k}
                (v : Vec (Fin k × Fin k) n)
                (f : (i : Fin n) → xs ! proj₁ (v ! i)
                                 ≡ xs ! proj₂ (v ! i))
                (ht₁ : HOTerm (Fin k) v x y)
                (ht₂ : HOTerm (Fin k) v x y) where
    open import sets.fin

    W : Edges (Fin k) _
    W = fin-graph (Fin k) v

    env : Env W X
    env = fin-env v xs f

    open WithDec X W (fin-graph-dec (Fin k) v _≟_)
    open WithEnv env

    t₁ : Term W x y
    t₁ = term ht₁

    t₂ : Term W x y
    t₂ = term ht₂

    solve : linearize t₁ ≡ linearize t₂
          → evalT t₁ ≡ evalT t₂
    solve p = run-solver t₁ t₂ p
open Solver public using (solve)
