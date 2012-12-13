{-# OPTIONS --without-K #-}
module equality.solver.core where

open import sum
open import decidable
open import level using (_⊔_)
open import equality.core

Graph : ∀ {i} (X : Set i) → ∀ k → Set _
Graph X k = X → X → Set k

_⇒_ : ∀ {i k k'}{X : Set i}
     → Graph X k → Graph X k' → Set _
W ⇒ U = ∀ {x y} → W x y → U x y
infixr 2 _⇒_

Env : ∀ {i k} {X : Set i} → Graph X k → Set _
Env W = W ⇒ _≡_

total-space : ∀ {i k}{X : Set i} → Graph X k → Set _
total-space {X = X} W = Σ (X × X) (uncurry W)

lift-total : ∀ {i k}{X : Set i}(W : Graph X k)
           → ∀ {x y} → W x y → total-space W
lift-total W {x}{y} w = ((x , y) , w)

record Involution {i k}{X : Set i}(W : Graph X k) : Set (i ⊔ k) where
  field
    τ : ∀ {x y} → W x y → W y x
    τ-τ : ∀ {x y}(w : W x y) → τ (τ w) ≡ w

record EnvInvolution {i k}{X : Set i}(W : Graph X k)(env : Env W) : Set (i ⊔ k) where
  field
    inv : Involution W

  open Involution inv

  field
    τ-correct : ∀ {x y}(w : W x y)
              → env (τ w) ≡ sym (env w)

  open Involution inv public

record DecGraph {i k}{X : Set i}(W : Graph X k) : Set (i ⊔ k) where
  field
    _≟_ : ∀ {x y y'}(w : W x y)(u : W x y')
        → Dec (Σ (y ≡ y') λ q → subst (W x) q w ≡ u)
    _≟'_ : ∀ {x x' y}(w : W x y)(u : W x' y)
         → Dec (Σ (x ≡ x') λ q → subst (λ x → W x y) q w ≡ u)
