{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import function.core
open import category2.structure
open import category2.category
open import category2.functor.core
open import category2.trans.core
open import category2.trans.ops
open import category2.trans.hlevel
open import function.extensionality

module category2.trans.properties {i}{j}{i'}{j'}
  (C : Category i j)(D : Category i' j') where

open as-category D
open as-category₀ (Func₀ C D)

private
  nat-right-unit : {F G : Functor C D}
                → (α : Nat F G)
                → α ∘ id ≡ α
  nat-right-unit {F}{G} (nt α α-nat) =
    nat-equality trans-right-unit
    where
      trans-right-unit : (λ X → α X ∘ id) ≡ α
      trans-right-unit = ext' λ X → right-id (α X)

  nat-left-unit : {F G : Functor C D}
                → (α : Nat F G)
                → id ∘ α ≡ α
  nat-left-unit {F}{G} (nt α α-nat) =
    nat-equality trans-left-unit
    where
      trans-left-unit : (λ X → id ∘ α X) ≡ α
      trans-left-unit = ext' λ X → left-id (α X)

  nat-assoc : {F G H K : Functor C D}
            → (α : Nat F G)
            → (β : Nat G H)
            → (γ : Nat H K)
            → (γ ∘ β) ∘ α ≡ γ ∘ (β ∘ α)
  nat-assoc {F}{G}{H}{K} (nt α α-nat) (nt β β-nat) (nt γ γ-nat) =
    nat-equality (ext' trans-assoc)
    where
      trans-assoc : ∀ X → γ X ∘ β X ∘ α X ≡ γ X ∘ (β X ∘ α X)
      trans-assoc X = assoc _ _ _

Func : Category _ _
Func = mk-category record
  { obj = Functor C D
  ; hom = Nat
  ; id = λ _ → id
  ; _∘_ = _∘_
  ; trunc = nat-hset
  ; left-id = nat-left-unit
  ; right-id = nat-right-unit
  ; assoc = λ α β γ → nat-assoc γ β α }
