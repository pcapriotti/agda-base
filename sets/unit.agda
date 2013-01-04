
{-# OPTIONS --without-K  #-}

module sets.unit where

record ⊤ : Set where
  constructor tt

⊤-elim : (P : ⊤ → Set) → P tt → (x : ⊤) → P x
⊤-elim P ptt tt = ptt
