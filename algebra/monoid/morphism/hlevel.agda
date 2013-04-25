{-# OPTIONS --without-K #-}

module algebra.monoid.morphism.hlevel where

open import equality.core
open import function.isomorphism
open import function.extensionality
open import function.overloading
import category.graph.morphism as G
open import category.graph.trivial
open import category.category.core
open import category.functor.core
open import category.functor.hlevel
open import algebra.monoid.core
open import algebra.monoid.morphism.core
open import hott.hlevel
open import overloading.core

morph-equality-iso : ∀ {i j}{M : Monoid i}{N : Monoid j}
                     {f g : Morphism M N}
                   → (apply f ≡ apply g)
                   ≅ (f ≡ g)
morph-equality-iso {M = M}{N}{f}{g} = begin
    apply f ≡ apply g
  ≅⟨ sym≅ trivial-morphism-equality ⟩
    (trivial-morphism (apply f) ≡ trivial-morphism (apply g))
  ≅⟨ func-equality-iso ⟩
    (functor f ≡ functor g)
  ≅⟨ iso≡ (sym≅ morphism-functor-iso) ⟩
    (f ≡ g)
  ∎
  where
    open ≅-Reasoning

morph-equality : ∀ {i j}{M : Monoid i}{N : Monoid j}
              → {f g : Morphism M N}
              → apply f ≡ apply g
              → f ≡ g
morph-equality = apply morph-equality-iso

morph-hlevel : ∀ {i j}(M : Monoid i)(N : Monoid j)
             → h 2 (Morphism M N)
morph-hlevel M N f g = iso-hlevel morph-equality-iso lem
  where
    lem : h 1 (apply f ≡ apply g)
    lem = (Π-hlevel λ _ → mtrunc _ _) _ _
      where open as-monoid N
