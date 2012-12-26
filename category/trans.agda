{-# OPTIONS --without-K #-}

open import level using (_⊔_)
open import category.category
open import category.functor using
  (Functor; module Functor)
open import equality.core
open import equality.calculus using (_⊚_; _⁻¹)
open import equality.reasoning

module category.trans {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

open Category using (obj; hom)

record Nat (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  constructor nat-trans
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

Compose : {F G H : Functor C D} → Nat G H → Nat F G → Nat F H
Compose {F}{G}{H} (nat-trans α α-nat) (nat-trans β β-nat) = nat-trans γ γ-nat
  where
    open Category D using (_∘_; associativity)
    open Functor
    open ≡-Reasoning

    γ : ∀ X → hom D (apply F X) (apply H X)
    γ X = α X ∘ β X

    γ-nat : ∀ {X Y} (f : hom C X Y)
          → γ Y ∘ map F f ≡ map H f ∘ γ X
    γ-nat {X}{Y} f = begin
        γ Y ∘ map F f
      ≡⟨ associativity _ _ _ ⟩
        α Y ∘ (β Y ∘ map F f)
      ≡⟨ cong (_∘_ (α Y)) (β-nat f) ⟩
        α Y ∘ (map G f ∘ β X)
      ≡⟨ sym (associativity _ _ _) ⟩
        α Y ∘ map G f ∘ β X
      ≡⟨ cong (λ z → z ∘ β X) (α-nat f) ⟩
        map H f ∘ α X ∘ β X
      ≡⟨ associativity _ _ _ ⟩
        map H f ∘ γ X
      ∎

record NatEq (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  constructor nat-eq
  field
    apply : Nat F G
    invert : Nat G F

coerce₁ : {F G : Functor C D}
        → F ≡ G → NatEq F G
coerce₁ {F} {.F} refl = nat-eq (Id F) (Id F)
