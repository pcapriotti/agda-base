{-# OPTIONS --type-in-type --without-K #-}

open import category.category.core

module category.yoneda.lemma (C : Category) where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.overloading
open import function.extensionality
open import category.graph
open import category.functor.core
open import category.instances.set
open import category.trans.core
open import category.trans.hlevel
open import category.yoneda.core C

open as-category C

-- Yoneda lemma
y-iso : (X : obj C)(F : Functor C set)
      → (hom-func X ⇒ F) ≅ proj₁ (apply F X)
y-iso X F = iso f g H K
  where
    f : (hom-func X ⇒ F) → proj₁ (apply F X)
    f (nt α α-nat) = α X id

    g : proj₁ (apply F X) → (hom-func X ⇒ F)
    g u = record
      { α = λ Y f → map F f u
      ; α-nat = λ h → ext' λ f → ext-inv (map-hom F h f) u }

    H : (α : hom-func X ⇒ F) → g (f α) ≡ α
    H (nt α α-nat) = nat-equality
      ( ext' λ Y
      → ext λ f
      → ext-inv (sym (α-nat f)) id
      ⊚ cong (α Y) (right-id f))

    K : (u : proj₁ (apply F X)) → f (g u) ≡ u
    K u = ext-inv (map-id F X) u
