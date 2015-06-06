{-# OPTIONS --without-K  #-}

module sets.empty where

open import level

data ⊥ {i} : Set i where

⊥-elim : ∀ {i j}{A : Set j} → ⊥ {i} → A
⊥-elim ()

¬_ : ∀ {i} → Set i → Set i
¬ X = X → ⊥ {lzero}
infix 3 ¬_
