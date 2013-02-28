{-# OPTIONS --without-K #-}

open import level
open import sum
open import category.category renaming (_∘_ to _⋆_)
open import category.functor
open import category.trans
  using (_⇒_; nt; module Nat)
open import equality.core
open import hott.hlevel

module category.kan-extension {i₀ j₀ i₁ j₁ i₂ j₂}
  {C : Category i₀ j₀}{C' : Category i₁ j₁}{D : Category i₂ j₂} where

record Extension (K : Functor C C')(G : Functor C D)
               : Set (i₀ ⊔ j₀ ⊔ i₁ ⊔ i₂ ⊔ j₁ ⊔ j₂) where
  constructor extension
  field
    F : Functor C' D
    counit : F ∘ K ⇒ G

private
  module Universality {K : Functor C C'}{G : Functor C D}
                      (ext : Extension K G) where
    open Extension ext
    open Nat counit
      renaming ( α to ε
               ; α-nat to ε-nat )
    open Functor

    ExtUniv : Extension K G → Set _
    ExtUniv (extension S (nt α _)) = Σ (S ⇒ F) λ { (nt β _) →
      (∀ X → ε X ⋆ β (apply K X) ≡ α X) }
open Universality public

record Ran (K : Functor C C')(G : Functor C D)
         : Set (i₀ ⊔ j₀ ⊔ i₁ ⊔ i₂ ⊔ j₁ ⊔ j₂) where
  field
    ext : Extension K G
    ext-univ : (ext' : Extension K G) → contr (ExtUniv ext ext')

  open Extension ext public
