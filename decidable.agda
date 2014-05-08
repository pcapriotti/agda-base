{-# OPTIONS --without-K #-}

module decidable where

open import sets.empty using (⊥; ¬_)
open import sets.unit using (⊤; tt)

-- Decidable relations.

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

True : {P : Set} → Dec P → Set
True (yes _) = ⊤
True (no _) = ⊥

witness : {P : Set}{d : Dec P} → True d → P
witness {d = yes x} _ = x
witness {d = no _} ()

decide : {P : Set} {d : Dec P} → P → True d
decide {d = yes p} = λ _ → tt
decide {d = no f} = f
