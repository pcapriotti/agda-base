{-# OPTIONS --without-K #-}

module algebra.monoid.hlevel where

open import sum
open import equality.core
open import function.extensionality
open import function.isomorphism
  hiding (apply)
open import sets.unit
import category.graph as Graph
open import category.category
open import category.functor
open import algebra.monoid.core
open import algebra.monoid.morphism
open import hott.hlevel

open Morphism
open Graph.Graph

morph-equality-iso : ∀ {i j}{M : Monoid i}{N : Monoid j}
                     {f g : Morphism M N}
                   → (f ≡ g)
                   ≅ (map f ≡ map g)
morph-equality-iso {M = M}{N}{f}{g} = begin
    (f ≡ g)
  ≅⟨ func-equality-iso ⟩
    Functor.morph f ≡ Functor.morph g
  ≅⟨ iso≡ Graph.morphism-structure-iso ⟩
    ( (Functor.apply f , λ {x}{y} → map f)
    ≡ (Functor.apply g , λ {x}{y} → map g))
  ≅⟨ sym≅ Σ-split-iso ⟩
    Σ (Functor.apply f ≡ Functor.apply g) (λ p
      → (λ {x}{y} → subst Graph.IsMorphism p
                      (Functor.map f {x}{y}))
      ≡ map g)
  ≅⟨ Σ-cong-iso ( iso≡ Π-left-unit
               ⊚≅ contr-⊤-iso (h↑ ⊤-contr tt tt) )
                (λ _ → refl≅) ⟩
    (⊤ × ((λ {x}{y} → Functor.map f {x}{y}) ≡ map g))
  ≅⟨ ×-left-unit ⟩
    ((λ {x}{y} → Functor.map f {x}{y}) ≡ map g)
  ≅⟨ iso≡ ( sym≅ impl-iso ⊚≅ Π-left-unit
         ⊚≅ sym≅ impl-iso ⊚≅ Π-left-unit) ⟩
    map f ≡ map g
  ∎
  where
    open ≅-Reasoning

    _⊚≅_ = trans≅
    infixl 4 _⊚≅_

morph-equality : ∀ {i j}{M : Monoid i}{N : Monoid j}
              → {f g : Morphism M N}
              → map f ≡ map g
              → f ≡ g
morph-equality = invert morph-equality-iso

morph-hlevel : ∀ {i j}(M : Monoid i)(N : Monoid j)
             → h 2 (Morphism M N)
morph-hlevel M N = iso-hlevel (sym≅ Graph.morphism-structure-iso)
    ( Σ-hlevel (Graph.morph-hlevel (h! ⊤-contr)
                  (λ _ _ → trunc))
               (λ m → h↑
                  ( is-func-prop {C = cat M}
                                 {D = cat N} m)) )
  where open cat-interface (cat N)
