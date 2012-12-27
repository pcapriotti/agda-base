{-# OPTIONS --without-K #-}

open import level
open import sum
open import category.category
open import category.functor
open import category.trans
  using (_⇒_; nt; module Nat)
open import equality.core
open import hott.hlevel

module category.kan-extension {i₀ j₀ i₁ j₁ i₂ j₂}
  {C : Category i₀ j₀}{C' : Category i₁ j₁}{D : Category i₂ j₂}
  (K : Functor C C')(G : Functor C D) where

record Extension : Set (i₀ ⊔ j₀ ⊔ i₁ ⊔ i₂ ⊔ j₁ ⊔ j₂) where
  constructor extension
  field
    F : Functor C' D
    counit : F ∘ K ⇒ G

private
  module Universality (ext : Extension) where
    open Extension ext public
    open Nat counit
      renaming ( α to ε
               ; α-nat to ε-nat )
    open Functor

    ExtUniv : Extension → Set _
    ExtUniv (extension S (nt α _)) = Σ (S ⇒ F) λ { (nt β _) →
      (∀ X → ε X ⋆ β (apply K X) ≡ α X) }
      where
        open Category D using ()
          renaming (_∘_ to _⋆_)

record Ran : Set (i₀ ⊔ j₀ ⊔ i₁ ⊔ i₂ ⊔ j₁ ⊔ j₂) where
  field ext : Extension

  open Universality ext

  field ext-univ : (ext' : Extension) → contr (ExtUniv ext')

  open Universality ext public
