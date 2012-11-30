
{-# OPTIONS --without-K  #-}

module decidable where

open import level            using (Level)
open import base_types.empty using (⊥)

infix 3 ¬_

¬_ : {l : Level} → Set l → Set l
¬ P = P → ⊥

-- Decidable relations.

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
