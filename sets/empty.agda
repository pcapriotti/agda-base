{-# OPTIONS --without-K  #-}

module sets.empty where

open import level using ()

data ⊥ : Set where

¬_ : ∀ {i} → Set i → Set i
¬ X = X → ⊥