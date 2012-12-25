{-# OPTIONS --without-K #-}

open import level using (_⊔_)
open import category.category
open import category.functor
open import equality.core

module category.trans {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

record Nat (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  open Category using (obj; hom)
  open Functor using (apply; map)
  open Category D using (_∘_)

  field
    α : ∀ X → hom D (apply F X) (apply G X)
    nat : ∀ {X Y} (f : hom C X Y)
        → α Y ∘ map F f ≡ map G f ∘ α X
