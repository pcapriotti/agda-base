{-# OPTIONS --without-K #-}
open import solver.equality.core
module solver.equality.list {i k}{X : Set i}(W : Graph X k) where

open import level using (_⊔_)
open import equality.core hiding (singleton)
open import equality.calculus
open import equality.reasoning
open import hott.hlevel

open import category.free.list public
  renaming (List to FList)

List : Graph X (i ⊔ k)
List = FList W

module WithInvolution (inv : Involution W) where
  open Involution inv

  reverse : ∀ {x y} → List x y → List y x
  reverse nil = nil
  reverse (w ∷ ws) = reverse ws ++ (τ w ∷ nil)

  reverse++ : ∀ {x y z} (ws : List x y) (us : List y z)
            → reverse (ws ++ us)
            ≡ reverse us ++ reverse ws
  reverse++ nil us = sym (nil-right-unit (reverse us))
  reverse++ (w ∷ ws) us =
      cong (λ α → α ++ (τ w ∷ nil)) (reverse++ ws us)
    ⊚ sym (++-assoc (reverse us) (reverse ws) (τ w ∷ nil))

  reverse-reverse : ∀ {x y} (ws : List x y)
                  → reverse (reverse ws) ≡ ws
  reverse-reverse nil = refl
  reverse-reverse (w ∷ ws) =
      reverse++ (reverse ws) (τ w ∷ nil)
    ⊚ cong₂ _∷_ (τ-τ w) (reverse-reverse ws)

module WithEnv {j}{X' : Set j}(env : Env W X') where
  open ≡-Reasoning
  
  eval : Env List X'
  eval = record { imap = imap env ; gmap = go }
    where
      go : ∀ {x y} → List x y → imap env x ≡ imap env y
      go nil = refl
      go (w ∷ ws) = gmap env w ⊚ go ws

  singleton : ∀ {x y}(w : W x y) → gmap eval (w ∷ nil) ≡ gmap env w
  singleton w = left-unit (gmap env w)

  eval++ : ∀ {x y z}(ws : List x y)(us : List y z)
         → gmap eval (ws ++ us) ≡ gmap eval ws ⊚ gmap eval us
  eval++ nil us = refl
  eval++ (w ∷ ws) us = begin
      gmap env w ⊚ gmap eval (ws ++ us)
    ≡⟨ cong (λ α → gmap env w ⊚ α) (eval++ ws us) ⟩
      gmap env w ⊚ (gmap eval ws ⊚ gmap eval us)
    ≡⟨ sym (associativity (gmap env w) (gmap eval ws) (gmap eval us)) ⟩
      gmap env w ⊚ gmap eval ws ⊚ gmap eval us
    ∎

module WithEnvInvolution {j}{X' : Set j}(env : Env W X') (env-inv : EnvInvolution W env) where
  open EnvInvolution env-inv
  open WithEnv env
  open WithInvolution inv
  open ≡-Reasoning

  reverse-inv : ∀ {x y}(t : List x y)
              → gmap eval (reverse t) ≡ (gmap eval t) ⁻¹
  reverse-inv nil = refl
  reverse-inv (w ∷ ws) = begin
      gmap eval (reverse ws ++ (τ w ∷ nil))
    ≡⟨ eval++ (reverse ws) (τ w ∷ nil) ⟩
      gmap eval (reverse ws) ⊚ gmap eval (τ w ∷ nil)
    ≡⟨ cong₂ _⊚_ (reverse-inv ws)
                (singleton (τ w) ⊚ τ-correct w) ⟩
      gmap eval ws ⁻¹ ⊚ gmap env w ⁻¹
    ≡⟨ sym (inverse-comp (gmap env w) (gmap eval ws)) ⟩
      gmap eval (w ∷ ws) ⁻¹
    ∎
