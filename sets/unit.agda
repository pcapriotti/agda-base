{-# OPTIONS --without-K  #-}

module sets.unit where

open import level

record ⊤ {i : Level} : Set i where
  constructor tt

⊤-elim : ∀ {i j} (P : ⊤ {i} → Set j) → P tt → (x : ⊤) → P x
⊤-elim P ptt tt = ptt
