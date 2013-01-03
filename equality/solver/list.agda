{-# OPTIONS --without-K #-}
open import equality.solver.core
module equality.solver.list {i k}{X : Set i}(W : Graph X k) where

open import level using (_⊔_)
open import equality.core hiding (singleton)
open import equality.calculus
open import equality.reasoning
open import hott.hlevel

data List : Graph X (i ⊔ k) where
  nil : ∀ {x} → List x x
  _∷_ : ∀ {x y z}
      → W x y
      → List y z
      → List x z
infixr 5 _∷_

private
  module HLevel (hX : h 3 X)(hW : h 2 (total-space W)) where
    open import decidable
    open import sum
    open import sets.empty
    open import sets.unit
    open import function.extensionality
    open import function.isomorphism
    open import w renaming (W to W-type)
    open import hott.hlevel.properties
    open import hott.univalence.properties

    I : Set i
    I = X × X 

    A : I → Set _
    A (x , y) = (x ≡ y) ⊎ Σ (total-space W) λ { ((x' , y') , w) → (x' ≡ x) }

    A-hlevel : (i : I) → h 2 (A i)
    A-hlevel (x , y) = ⊎-hlevel {p = tt} (hX x y)
      (Σ-hlevel hW (λ { ((x' , _) , _) → hX x' x }))

    B : (i : I) → A i → Set _
    B (x , .x) (inj₁ refl) = ⊥
    B (.x , z) (inj₂ (((x , y) , w) , refl)) = ⊤

    r : (i : I)(a : A i) → B i a → I
    r (x , .x) (inj₁ refl) ()
    r (.x , z) (inj₂ (((x , y) , w) , refl)) _ = y , z

    List' : X → X → Set _
    List' x y = W-type I A B r (x , y)

    list-iso : (x y : X) → List' x y ≅ List x y
    list-iso _ _ = iso f g iso₁ iso₂
      where
        f : {x y : X} → List' x y → List x y
        f {x}{.x} (sup (inj₁ refl) _) = nil
        f {.x}{z} (sup (inj₂ (((x , y) , w) , refl)) u) = w ∷ f (u tt)

        g : {x y : X} → List x y → List' x y
        g {x}{.x} nil = sup (inj₁ refl) (λ ())
        g {.x}{.z} (_∷_ {x}{y}{z} w ws) =
          sup (inj₂ (((x , y) , w) , refl)) (λ _ → g ws)

        iso₁ : {x y : X}(ws : List' x y) → g (f ws) ≡ ws
        iso₁ {x}{.x} (sup (inj₁ refl) _) = cong (sup (inj₁ refl)) (ext' λ ())
        iso₁ {.x}{z} (sup (inj₂ (((x , y) , w) , refl)) u) =
          cong (sup (inj₂ (((x , y) , w) , refl))) (ext λ { tt → iso₁ (u tt) })

        iso₂ : {x y : X}(ws : List x y) → f (g ws) ≡ ws
        iso₂ {x}{.x} nil = refl
        iso₂ (w ∷ ws) = cong (_∷_ w) (iso₂ ws)

    list-hlevel : (x y : X) → h 2 (List x y)
    list-hlevel x y = iso-hlevel (list-iso x y) (w-hlevel (λ { (x , y) → A-hlevel (x , y) }) (x , y))

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