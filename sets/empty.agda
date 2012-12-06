{-# OPTIONS --without-K  #-}

module sets.empty where

open import level using ()

data ⊥ : Set where

⊥-elim : ∀ {i}{A : Set i} → ⊥ → A
⊥-elim ()

¬_ : ∀ {i} → Set i → Set i
¬ X = X → ⊥
infix 3 ¬_
