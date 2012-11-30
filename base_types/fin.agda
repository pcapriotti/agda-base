
{-# OPTIONS --without-K  #-}

module base_types.fin where

open import base_types.nat using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin n
  suc  : {n : ℕ} → Fin n → Fin (suc n)
