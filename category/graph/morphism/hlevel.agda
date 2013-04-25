{-# OPTIONS --without-K #-}

module category.graph.morphism.hlevel where

open import sum
open import function.isomorphism
open import category.graph.core
open import category.graph.morphism.core
open import overloading

morphism-structure-iso : ∀ {i₁ j₁ i₂ j₂}
                         {W : Graph i₁ j₁}
                         {U : Graph i₂ j₂}
                       → ( Σ (∣ W ∣ → ∣ U ∣) λ f
                         → IsMorphism {W = W}{U = U} f )
                       ≅ Morphism W U
morphism-structure-iso = bundle-structure-iso IsMorphism
