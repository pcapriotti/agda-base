{-# OPTIONS --without-K #-}

open import level using (_⊔_)
open import category.category
open import category.functor using
  (Functor; module Functor)
open import equality.core
open import equality.calculus using (_⊚_; _⁻¹)

module category.trans {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

record Nat (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  constructor nat-trans
  open Category using (obj; hom)
  open Functor using (apply; map)
  open Category D using (_∘_)
  field
    α : ∀ X → hom D (apply F X) (apply G X)
    α-nat : ∀ {X Y} (f : hom C X Y)
          → α Y ∘ map F f ≡ map G f ∘ α X

Id : (F : Functor C D) → Nat F F
Id F = nat-trans (λ X → id (apply F X))
                 (λ f → left-unit (map F f)
                      ⊚ right-unit (map F f) ⁻¹)
  where
    open Functor
    open Category D

record NatEq (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  constructor nat-eq
  field
    apply : Nat F G
    invert : Nat G F

coerce₁ : {F G : Functor C D}
        → F ≡ G → NatEq F G
coerce₁ {F} {.F} refl = nat-eq (Id F) (Id F)
