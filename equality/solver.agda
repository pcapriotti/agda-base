{-# OPTIONS --without-K #-}
module equality.solver {i}(X : Set i) where

open import decidable
open import sum
open import function using (_∘_)
open import level using (lsuc; _⊔_)
open import equality.core hiding (singleton)
open import equality.reasoning
open import equality.calculus
open import sets.nat using (ℕ)
open import sets.fin hiding (_≟_)
open import sets.vec

open import equality.solver.core
open import equality.solver.builder

open ≡-Reasoning

lem-rewrite : {x y y' z : X}
            → (p : x ≡ y)(q : y ≡ z)
            → (r r' : y' ≡ y)
            → (r ≡ r')
            → p ⊚ q ≡ (p ⊚ r ⁻¹) ⊚ (r' ⊚ q)
lem-rewrite refl q r .r refl =
    sym (cong (λ α → α ⊚ q) (right-inverse r))
  ⊚ associativity (sym r) r q

module WithDec {n k} (W : Graph (Fin n) k)(dec : DecGraph W) where
  open DecGraph dec

  module Terms where
    import equality.solver.term as M
    open M W public
  open Terms hiding (module WithEnv)

  module Words where
    import equality.solver.word as M
    open M W public
  open Words hiding (module WithEnv)

  module Lists where
    import equality.solver.list as L
    open L Word public
    open WithInvolution word-inv public
  open Lists hiding (module WithEnv)

  fuse : ∀ {x y z} → List y x → List y z → List x z
  fuse {z = z} (fwd w ∷ ws) (fwd u ∷ us) with u ≟ w
  ... | yes (q , _) = fuse ws (subst (λ α → List α z) q us)
  ... | no _ = reverse (fwd w ∷ ws) ++ (fwd u ∷ us)
  fuse {z = z} (inv w ∷ ws) (inv u ∷ us) with u ≟' w
  ... | yes (q , _) = fuse ws (subst (λ α → List α z) q us)
  ... | no _ = reverse (inv w ∷ ws) ++ (inv u ∷ us)
  fuse ws us = reverse ws ++ us

  linearize : ∀ {x y} → Term x y → List x y
  linearize null = nil
  linearize (var i) = fwd i ∷ nil
  linearize (g * f) = fuse (reverse (linearize g)) (linearize f)
  linearize (inv f) = reverse (linearize f)

  module WithEnv (env : Env W X) where
    open Terms.WithEnv env
      renaming (eval to envT)
    open Words.WithEnv env
      renaming (eval to envW)
    open Lists.WithEnv envW
      renaming (eval to envL)
    open Lists.WithEnvInvolution envW word-env-inv
    evalT = gmap envT
    evalW = gmap envW
    evalL = gmap envL

    fuse-correct : ∀ {x y z}(ws : List y x)(us : List y z)
                 → evalL (fuse ws us) ≡ evalL (reverse ws ++ us)
    fuse-correct {x}{y}{z} (fwd w ∷ ws) (fwd u ∷ us) with u ≟ w
    ... | yes (q , p) = begin
        evalL (fuse ws us')
      ≡⟨ fuse-correct ws us' ⟩
        evalL (reverse ws ++ us')
      ≡⟨ eval++ (reverse ws) us' ⟩
        evalL (reverse ws) ⊚ evalL us'
      ≡⟨ cong (λ α → α ⊚ evalL us') (reverse-inv ws) ⟩
        evalL ws ⁻¹ ⊚ evalL us'
      ≡⟨ lem-rewrite (evalL ws ⁻¹) (evalL us')
                     (evalW (fwd w)) (evalW (fwd u'))
                     (cong (gmap env) (sym p)) ⟩
        (evalL ws ⁻¹ ⊚ evalW (fwd w) ⁻¹) ⊚ (evalW (fwd u') ⊚ evalL us')
      ≡⟨ cong (λ α → (evalL ws ⁻¹ ⊚ evalW (fwd w) ⁻¹) ⊚ α) (lem q u us) ⟩
        (evalL ws ⁻¹ ⊚ evalW (fwd w) ⁻¹) ⊚ (evalW (fwd u) ⊚ evalL us)
      ≡⟨ cong (λ α → α ⊚ (evalW (fwd u) ⊚ evalL us))
              (sym (inverse-comp (evalW (fwd w)) (evalL ws))) ⟩
        (evalW (fwd w) ⊚ evalL ws) ⁻¹ ⊚ (evalW (fwd u) ⊚ evalL us)
      ≡⟨ cong (λ α → α ⊚ evalL (fwd u ∷ us))
              (sym (reverse-inv (fwd w ∷ ws))) ⟩
        evalL (reverse (fwd w ∷ ws)) ⊚ evalL (fwd u ∷ us)
      ≡⟨ sym (eval++ (reverse (fwd w ∷ ws)) (fwd u ∷ us)) ⟩
        evalL (reverse (fwd w ∷ ws) ++ (fwd u ∷ us))
      ∎
      where
        us' = subst (λ α → List α z) q us
        u' = subst (W y) q u

        lem : ∀ {x z z' y} (q : z ≡ z') (w : W x z) (ws : List z y)
             → evalW (fwd (subst (W x) q w))
             ⊚ evalL (subst (λ α → List α y) q ws)
             ≡ evalW (fwd w) ⊚ evalL ws
        lem refl w ws = refl

    ... | no _ = refl
    fuse-correct {x}{y}{z} (inv w ∷ ws) (inv u ∷ us) with u ≟' w
    ... | yes (q , p) = begin
        evalL (fuse ws us')
      ≡⟨ fuse-correct ws us' ⟩
        evalL (reverse ws ++ us')
      ≡⟨ eval++ (reverse ws) us' ⟩
        evalL (reverse ws) ⊚ evalL us'
      ≡⟨ cong (λ α → α ⊚ evalL us') (reverse-inv ws) ⟩
        evalL ws ⁻¹ ⊚ evalL us'
      ≡⟨ lem-rewrite (evalL ws ⁻¹) (evalL us')
                      (evalW (inv w)) (evalW (inv u'))
                      (cong (sym ∘ gmap env) (sym p)) ⟩
        (evalL ws ⁻¹ ⊚ evalW (inv w) ⁻¹) ⊚ (evalW (inv u') ⊚ evalL us')
      ≡⟨ cong (λ α → (evalL ws ⁻¹ ⊚ evalW (inv w) ⁻¹) ⊚ α)
              (lem q u us) ⟩
        (evalL ws ⁻¹ ⊚ evalW (inv w) ⁻¹) ⊚ (evalW (inv u) ⊚ evalL us)
      ≡⟨ cong (λ α → α ⊚ (evalW (inv u) ⊚ evalL us))
              (sym (inverse-comp (evalW (inv w)) (evalL ws))) ⟩
        (evalW (inv w) ⊚ evalL ws) ⁻¹ ⊚ (evalW (inv u) ⊚ evalL us)
      ≡⟨ cong (λ α → α ⊚ evalL (inv u ∷ us))
              (sym (reverse-inv (inv w ∷ ws))) ⟩
        evalL (reverse (inv w ∷ ws)) ⊚ evalL (inv u ∷ us)
      ≡⟨ sym (eval++ (reverse (inv w ∷ ws)) (inv u ∷ us)) ⟩
        evalL (reverse (inv w ∷ ws) ++ (inv u ∷ us))
      ∎
      where
        us' = subst (λ α → List α z) q us
        u' = subst (λ α → W α y) q u

        lem : ∀ {x z z' y} (q : z ≡ z') (w : W z x) (ws : List z y)
             → evalW (inv (subst (λ α → W α x) q w))
             ⊚ evalL (subst (λ α → List α y) q ws)
             ≡ evalW (inv w) ⊚ evalL ws
        lem refl w ws = refl
    ... | no _ = refl
    fuse-correct (fwd w ∷ ws) (inv u ∷ us) = refl
    fuse-correct (inv w ∷ ws) (fwd u ∷ us) = refl
    fuse-correct (fwd w ∷ ws) nil = refl
    fuse-correct (inv w ∷ ws) nil = refl
    fuse-correct nil us = refl

    linearize-correct : ∀ {x y}(t : Term x y)
                      → evalL (linearize t) ≡ evalT t
    linearize-correct null = refl
    linearize-correct (var w) = left-unit (gmap env w)
    linearize-correct (t₁ * t₂) = 
        fuse-correct (reverse (linearize t₁)) (linearize t₂)
      ⊚ (cong (λ α → evalL (α ++ linearize t₂))
              (reverse-reverse (linearize t₁))
      ⊚ (eval++ (linearize t₁) (linearize t₂)
      ⊚ cong₂ _⊚_ (linearize-correct t₁) (linearize-correct t₂)))
      
    linearize-correct (inv t) =
      reverse-inv (linearize t) ⊚
      cong sym (linearize-correct t)

    solve : ∀ {x y} (t₁ t₂ : Term x y)
          → linearize t₁ ≡ linearize t₂
          → evalT t₁ ≡ evalT t₂
    solve t₁ t₂ p = begin
        evalT t₁
      ≡⟨ sym (linearize-correct t₁) ⟩
        evalL (linearize t₁)
      ≡⟨ cong evalL p ⟩
        evalL (linearize t₂)
      ≡⟨ linearize-correct t₂ ⟩
        evalT t₂
      ∎
