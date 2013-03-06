{-# OPTIONS --without-K #-}

open import level using (_⊔_)
open import sum
open import category.graph hiding (Id)
open import category.structure
open import category.category renaming (_∘_ to _⋆_)
open import category.functor.core using
  (Functor; module Functor)
open import equality.core
open import equality.calculus using (_⊚_; _⁻¹)
open import equality.reasoning

module category.trans.core {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

open Functor using (apply; map)
open overloaded IsCategory C
open overloaded IsCategory D

Trans : Functor C D → Functor C D → Set _
Trans F G = (X : obj C) → hom D (apply F X) (apply G X)

nat-equation : (F G : Functor C D)(α : Trans F G) → total C → Set _
nat-equation F G α ((X , Y), f) =
  α Y ⋆ map F f ≡ map G f ⋆ α X

natural : (F G : Functor C D) → Trans F G → Set _
natural F G α = ∀ {X Y} (f : hom C X Y) → nat-equation F G α ((X , Y) , f)

record Nat (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  constructor nt
  field
    α : Trans F G
    α-nat : natural F G α

_⇒_ : Functor C D → Functor C D → Set _
_⇒_ = Nat
infixr 1 _⇒_

Id : (F : Functor C D) → Nat F F
Id F = nt (λ X → id (apply F X))
          ( λ f → left-unit (map F f)
                ⊚ right-unit (map F f) ⁻¹ )

Compose : {F G H : Functor C D} → Nat G H → Nat F G → Nat F H
Compose {F}{G}{H} (nt α α-nat) (nt β β-nat) = (nt γ γ-nat)
  where
    open ≡-Reasoning

    γ : ∀ X → hom D (apply F X) (apply H X)
    γ X = α X ⋆ β X

    γ-nat : ∀ {X Y} (f : hom C X Y)
          → γ Y ⋆ map F f ≡ map H f ⋆ γ X
    γ-nat {X}{Y} f = begin
        γ Y ⋆ map F f
      ≡⟨ associativity _ _ _ ⟩
        α Y ⋆ (β Y ⋆ map F f)
      ≡⟨ cong (_⋆_ (α Y)) (β-nat f) ⟩
        α Y ⋆ (map G f ⋆ β X)
      ≡⟨ sym (associativity _ _ _) ⟩
        α Y ⋆ map G f ⋆ β X
      ≡⟨ cong (λ z → z ⋆ β X) (α-nat f) ⟩
        map H f ⋆ α X ⋆ β X
      ≡⟨ associativity _ _ _ ⟩
        map H f ⋆ γ X
      ∎

record NatEq (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  constructor nat-eq
  field
    nat-apply : Nat F G
    nat-invert : Nat G F

coerce₁ : {F G : Functor C D}
        → F ≡ G → NatEq F G
coerce₁ {F} {.F} refl = nat-eq (Id F) (Id F)
