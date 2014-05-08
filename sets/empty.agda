{-# OPTIONS --without-K  #-}

module sets.empty where

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬_ : Set → Set
¬ X = X → ⊥
infix 3 ¬_
