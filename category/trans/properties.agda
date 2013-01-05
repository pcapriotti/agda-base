{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import category.category renaming (_∘_ to _⋆_)
open import category.functor.core
  using (Functor; module Functor)
open import category.trans.core
open import category.trans.hlevel
open import function.extensionality

module category.trans.properties {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

open Functor

nat-right-unit : {F G : Functor C D}
              → (α : Nat F G)
              → α ∘ Id F ≡ α
nat-right-unit {F}{G} (nt α α-nat) =
  nat-equality trans-right-unit
  where
    trans-right-unit : (λ X → α X ⋆ id (apply F X)) ≡ α
    trans-right-unit = ext' λ X → right-unit (α X)

nat-left-unit : {F G : Functor C D}
              → (α : Nat F G)
              → Id G ∘ α ≡ α
nat-left-unit {F}{G} (nt α α-nat) =
  nat-equality trans-left-unit
  where
    trans-left-unit : (λ X → id (apply G X) ⋆ α X) ≡ α
    trans-left-unit = ext' λ X → left-unit (α X)

nat-assoc : {F G H K : Functor C D}
          → (α : Nat F G)
          → (β : Nat G H)
          → (γ : Nat H K)
          → γ ∘ β ∘ α ≡ γ ∘ (β ∘ α)
nat-assoc {F}{G}{H}{K} (nt α α-nat) (nt β β-nat) (nt γ γ-nat) =
  nat-equality (ext' trans-assoc)
  where
    trans-assoc : ∀ X → γ X ⋆ β X ⋆ α X ≡ γ X ⋆ (β X ⋆ α X)
    trans-assoc X = associativity _ _ _
