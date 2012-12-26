{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import category.category
open import category.functor
  using (Functor; module Functor)
open import category.trans.core
open import category.trans.hlevel
open import function.extensionality

module category.trans.properties {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

open Functor
open Category D using
  (id; right-unit; left-unit; associativity)
  renaming (_∘_ to _⋆_)

nat-right-unit : {F G : Functor C D}
              → (α : Nat F G)
              → α ∘ Id F ≡ α
nat-right-unit {F}{G} (nt α α-nat) =
  nat-equality F G _ _ trans-right-unit
  where
    trans-right-unit : (λ X → α X ⋆ id (apply F X)) ≡ α
    trans-right-unit = extensionality' _ _ (λ X → right-unit (α X))

nat-left-unit : {F G : Functor C D}
              → (α : Nat F G)
              → Id G ∘ α ≡ α
nat-left-unit {F}{G} (nt α α-nat) =
  nat-equality F G _ _ trans-left-unit
  where
    trans-left-unit : (λ X → id (apply G X) ⋆ α X) ≡ α
    trans-left-unit = extensionality' _ _ (λ X → left-unit (α X))

nat-assoc : {F G H K : Functor C D}
          → (α : Nat H K)
          → (β : Nat G H)
          → (γ : Nat F G)
          → α ∘ β ∘ γ ≡ α ∘ (β ∘ γ)
nat-assoc {F}{G}{H}{K} (nt α α-nat) (nt β β-nat) (nt γ γ-nat) =
  nat-equality F K _ _ (extensionality' _ _ trans-assoc)
  where
    trans-assoc : ∀ X → α X ⋆ β X ⋆ γ X ≡ α X ⋆ (β X ⋆ γ X)
    trans-assoc X = associativity _ _ _
