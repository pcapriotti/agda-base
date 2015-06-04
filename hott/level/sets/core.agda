{-# OPTIONS --without-K #-}
module hott.level.sets.core where

open import sum
open import equality.core
open import sets.unit
open import sets.empty
open import hott.level.core

⊤-contr : ∀ {i} → contr (⊤ {i})
⊤-contr = tt , λ { tt → refl }

⊥-prop : h 1 ⊥
⊥-prop x _ = ⊥-elim x
