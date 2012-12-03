
{-# OPTIONS --without-K  #-}

module sets.fin where

open import sets.nat using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin n
  suc  : {n : ℕ} → Fin n → Fin (suc n)
