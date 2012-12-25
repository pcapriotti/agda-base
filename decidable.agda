
{-# OPTIONS --without-K  #-}

module decidable where

open import level            using (Level)
open import sets.empty using (¬_)

-- Decidable relations.

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P