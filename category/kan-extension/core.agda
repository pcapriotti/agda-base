{-# OPTIONS --without-K #-}

open import category.category

module category.kan-extension.core {C C' D : Category} where

open import level
open import sum
open import function.core
open import function.overloading
open import category.functor
open import category.trans
open import equality.core
open import hott.hlevel

open as-category D

record Extension (K : Functor C C')(G : Functor C D) : Set where
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

    ExtUniv : Extension K G → Set _
    ExtUniv (extension S (nt α _)) = Σ (S ⇒ F) λ { (nt β _) →
      (∀ X → ε X ∘ β (apply K X) ≡ α X) }
open Universality public

record Ran (K : Functor C C')(G : Functor C D) : Set where
  field
    ext : Extension K G
    ext-univ : (ext' : Extension K G) → contr (ExtUniv ext ext')

  open Extension ext public
