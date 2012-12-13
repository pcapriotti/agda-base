{-# OPTIONS --without-K #-}
open import equality.solver.core
module equality.solver.list {i k} (X : Set i)(W : Graph X k) where

open import level using (_⊔_)
open import equality.core hiding (singleton)
open import equality.calculus
open import equality.reasoning

data List : Graph X (i ⊔ k) where
  nil : ∀ {x} → List x x
  _∷_ : ∀ {x y z}
      → W x y
      → List y z
      → List x z
infixr 5 _∷_

_++_ : ∀ {x y z} → List x y → List y z → List x z
nil ++ ws = ws
(u ∷ us) ++ ws = u ∷ (us ++ ws)
infixl 5 _++_

assoc++ : ∀ {x y z w}(ws : List x y)(us : List y z)(vs : List z w)
        → ws ++ (us ++ vs)
        ≡ ws ++ us ++ vs
assoc++ nil us vs = refl
assoc++ (w ∷ ws) us vs = cong (λ α → w ∷ α) (assoc++ ws us vs)

nil-right-inverse : ∀ {x y} (ws : List x y)
                  → ws ++ nil ≡ ws
nil-right-inverse nil = refl
nil-right-inverse (w ∷ ws) =
  cong (λ ws → w ∷ ws)
       (nil-right-inverse ws)

module WithInvolution (inv : Involution W) where
  open Involution inv

  reverse : ∀ {x y} → List x y → List y x
  reverse nil = nil
  reverse (w ∷ ws) = reverse ws ++ (τ w ∷ nil)

  reverse++ : ∀ {x y z} (ws : List x y) (us : List y z)
            → reverse (ws ++ us)
            ≡ reverse us ++ reverse ws
  reverse++ nil us = sym (nil-right-inverse (reverse us))
  reverse++ (w ∷ ws) us =
      cong (λ α → α ++ (τ w ∷ nil)) (reverse++ ws us)
    ⊚ sym (assoc++ (reverse us) (reverse ws) (τ w ∷ nil))

  reverse-reverse : ∀ {x y} (ws : List x y)
                  → reverse (reverse ws) ≡ ws
  reverse-reverse nil = refl
  reverse-reverse (w ∷ ws) =
      reverse++ (reverse ws) (τ w ∷ nil)
    ⊚ cong₂ _∷_ (τ-τ w) (reverse-reverse ws)

module WithEnv (env : Env W) where
  open ≡-Reasoning
  
  eval : Env List
  eval nil = refl
  eval (w ∷ ws) = env w ⊚ eval ws

  singleton : ∀ {x y}(w : W x y) → eval (w ∷ nil) ≡ env w
  singleton w = left-unit (env w)

  eval++ : ∀ {x y z}(ws : List x y)(us : List y z)
         → eval (ws ++ us) ≡ eval ws ⊚ eval us
  eval++ nil us = refl
  eval++ (w ∷ ws) us = begin
      env w ⊚ eval (ws ++ us)
    ≡⟨ cong (λ α → env w ⊚ α) (eval++ ws us) ⟩
      env w ⊚ (eval ws ⊚ eval us)
    ≡⟨ sym (associativity (env w) (eval ws) (eval us)) ⟩
      env w ⊚ eval ws ⊚ eval us
    ∎

module WithEnvInvolution (env : Env W) (env-inv : EnvInvolution W env) where
  open EnvInvolution env-inv
  open WithEnv env
  open WithInvolution inv
  open ≡-Reasoning

  reverse-inv : ∀ {x y}(t : List x y)
              → eval (reverse t) ≡ (eval t) ⁻¹
  reverse-inv nil = refl
  reverse-inv (w ∷ ws) = begin
      eval (reverse ws ++ (τ w ∷ nil))
    ≡⟨ eval++ (reverse ws) (τ w ∷ nil) ⟩
      eval (reverse ws) ⊚ eval (τ w ∷ nil)
    ≡⟨ cong₂ _⊚_ (reverse-inv ws)
                (singleton (τ w) ⊚ τ-correct w) ⟩
      eval ws ⁻¹ ⊚ env w ⁻¹
    ≡⟨ sym (inverse-comp (env w) (eval ws)) ⟩
      eval (w ∷ ws) ⁻¹
    ∎