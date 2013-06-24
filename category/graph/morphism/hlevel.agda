{-# OPTIONS --without-K #-}

module category.graph.morphism.hlevel where

open import sum
open import function.isomorphism
open import category.graph.core
open import category.graph.morphism.core
open import overloading

morphism-structure-iso : {W U : Graph}
                       → ( Σ (∣ W ∣ → ∣ U ∣) λ f
                         → IsMorphism {W = W}{U = U} f )
                       ≅ Morphism W U
morphism-structure-iso = bundle-structure-iso IsMorphism
