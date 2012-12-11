{-# OPTIONS --without-K #-}
module equality.solver {i}(X : Set i) where

open import decidable
open import sum
open import level using (lsuc; _⊔_)
open import equality.core
open import equality.reasoning
open import equality.calculus
open import sets.nat using (ℕ)
open import sets.fin
open import sets.vec

open ≡-Reasoning

Graph : ∀ k → Set _
Graph k = X → X → Set (i ⊔ k)

total-space : ∀ {k} → Graph k → Set (i ⊔ k)
total-space g = Σ (X × X) λ {(x , y) → g x y}

Env : ∀ k → Graph k → Set _
Env _ g = ∀ {x y} → g x y → x ≡ y

DecGraph : ∀ {k} → Graph k → Set (i ⊔ k)
DecGraph {k} g = (u v : total-space {k} g) → Dec (u ≡ v)

module Generic {k} (W : Graph k) where
  data Term : Graph k where
    null : ∀ {x} → Term x x
    var : ∀ {x y} → W x y → Term x y
    _*_ : ∀ {x y z} → Term y z → Term x y → Term x z
    inv : ∀ {x y} → Term y x → Term x y
  infixl 5 _*_

  data Word : Graph k where
    fwd : ∀ {x y} → W x y → Word x y
    inv : ∀ {x y} → W y x → Word x y

  wreverse : ∀ {x y} → Word x y → Word y x
  wreverse (fwd w) = inv w
  wreverse (inv w) = fwd w

  data List : Graph k where
    nil : ∀ {x} → List x x
    _∷_ : ∀ {x y z}
        → Word x y
        → List y z
        → List x z
  infixr 5 _∷_

  _++_ : ∀ {x y z} → List x y → List y z → List x z
  nil ++ ws = ws
  (u ∷ us) ++ ws = u ∷ (us ++ ws)
  infixr 5 _++_

  reverse : ∀ {x y} → List x y → List y x
  reverse nil = nil
  reverse (w ∷ ws) = reverse ws ++ (wreverse w ∷ nil)

  fuse : ∀ {x y z} → List y x → List y z → List x z
  fuse (i ∷ is) (j ∷ js) = {!!}
  fuse is js = reverse is ++ js

--   mutual
--     fuse : ∀ {x y z} → List z y → List x y → List x z
--     fuse nil js = js
--     fuse (i ∷ is) js = fuse₁ i refl is js
--     fuse (i ∺ is) js = fuse₂ i refl is js
-- 
--     fuse₁ : ∀ {x y z} i → (y ≡ target tenv i) → List z (source tenv i)
--        → List x y → List x z
--     fuse₁ {x} i p is (j ∷ js) = fuse-step₁ i j p is js (j ≟ i)
--     fuse₁ {x} i p is js =
--       reverse (i ∷ is) ++ subst (λ w → List x w) p js
-- 
--     fuse-step₁ : ∀ {x z} i j
--                → (target tenv j ≡ target tenv i)
--                → List z (source tenv i)
--                → List x (source tenv j)
--                → Dec (j ≡ i)
--                → List x z
--     fuse-step₁ {x} i j p is js (yes q)
--       = fuse is (subst (λ i → List x (source tenv i)) q js)
--     fuse-step₁ {x} i j p is js (no _)
--       = reverse (i ∷ is) ++ subst (List x) p (j ∷ js)
-- 
--     fuse₂ : ∀ {x y z} i → (y ≡ source tenv i) → List z (target tenv i)
--        → List x y → List x z
--     fuse₂ {x} i p is (j ∺ js) with j ≟ i
--     ... | yes q =
--       fuse is (subst (λ i → List x (target tenv i)) q js)
--     ... | no _ =
--       reverse (i ∺ is) ++ subst (λ w → List x w) p (j ∺ js)
--     fuse₂ {x} i p is js =
--       reverse (i ∺ is) ++ subst (λ w → List x w) p js
-- 
  linearize : {x y : X} → Term x y → List x y
  linearize null = nil
  linearize (var i) = fwd i ∷ nil
  linearize (g * f) = linearize f ++ linearize g
  linearize (inv f) = reverse (linearize f)

  module WithEnv (env : Env k W) where
    evalT : ∀ {x y} → Term x y → x ≡ y
    evalT null = refl
    evalT (var x) = env x
    evalT (g * f) = evalT f ⊚ evalT g
    evalT (inv t) = evalT t ⁻¹

    evalW : ∀ {x y} → Word x y → x ≡ y
    evalW (fwd w) = env w
    evalW (inv w) = env w ⁻¹

    wreverse-inv : ∀ {x y}(w : Word x y)
                 → evalW (wreverse w)
                 ≡ evalW w ⁻¹
    wreverse-inv (fwd w) = refl
    wreverse-inv (inv w) = sym (double-inverse (env w))

    evalL : ∀ {x y} → List x y → x ≡ y
    evalL nil = refl
    evalL (w ∷ ws) = evalW w ⊚ evalL ws

    oneW : ∀ {x y}(w : Word x y) → evalL (w ∷ nil) ≡ evalW w
    oneW w = left-unit (evalW w)

    eval++ : ∀ {x y z}(ws : List x y)(us : List y z)
           → evalL (ws ++ us) ≡ evalL ws ⊚ evalL us
    eval++ nil us = refl
    eval++ (w ∷ ws) us = begin
        evalW w ⊚ evalL (ws ++ us)
      ≡⟨ cong (λ α → evalW w ⊚ α) (eval++ ws us) ⟩
        evalW w ⊚ (evalL ws ⊚ evalL us)
      ≡⟨ sym (associativity (evalW w) (evalL ws) (evalL us)) ⟩
        evalW w ⊚ evalL ws ⊚ evalL us
      ∎
-- 
--     fuse-correct : ∀ {x y z}(is : List z y)(js : List x y)
--                  → evalL (fuse is js) ≡ evalL (reverse is ++ js)
--     fuse-correct nil js = refl
--     fuse-correct (i ∷ is) js = go i refl is js
--       where
--         go : ∀ {x y z} i
--            → (p : y ≡ target tenv i)
--            → (is : List z (source tenv i))
--            → (js : List x y)
--            → evalL (fuse₁ i p is js)
--            ≡ evalL (reverse (i ∷ is) ++ subst (List x) p js)
--         go i p is nil = refl
--         go {x} i p is (j ∷ js) with j ≟ i
--         ... | yes q = {!fuse-correct is js'!}
--           where
--             js' : List x (source tenv i)
--             js' = subst (λ j → List x (source tenv j)) q js
--         ... | no _ = {!!}
--           
-- 
--         go i p is (j ∺ js) = {!!}
--     fuse-correct (i ∺ is) js = {!!}

    reverse-inv : ∀ {x y}(t : List x y)
                → evalL (reverse t) ≡ (evalL t) ⁻¹
    reverse-inv nil = refl
    reverse-inv (w ∷ ws) = begin
        evalL (reverse ws ++ (wreverse w ∷ nil))
      ≡⟨ eval++ (reverse ws) (wreverse w ∷ nil) ⟩
        evalL (reverse ws) ⊚ evalL (wreverse w ∷ nil)
      ≡⟨ cong₂ _⊚_ (reverse-inv ws)
                  (oneW (wreverse w) ⊚ wreverse-inv w) ⟩
        evalL ws ⁻¹ ⊚ evalW w ⁻¹
      ≡⟨ sym (inverse-comp (evalW w) (evalL ws)) ⟩
        evalL (w ∷ ws) ⁻¹
      ∎

    linearize-correct : {x y : X}(t : Term x y)
                      → evalL (linearize t) ≡ evalT t
    linearize-correct null = refl
    linearize-correct (var w) = left-unit (env w)
    linearize-correct (t₁ * t₂) = begin
        evalL (linearize t₂ ++ linearize t₁)
      ≡⟨ eval++ (linearize t₂) (linearize t₁) ⟩
        evalL (linearize t₂) ⊚ evalL (linearize t₁)
      ≡⟨ cong₂ _⊚_ (linearize-correct t₂) (linearize-correct t₁) ⟩
        evalT t₂ ⊚ evalT t₁
      ∎
    linearize-correct (inv t) =
      reverse-inv (linearize t) ⊚
      cong sym (linearize-correct t)

    solve : {x y : X} (t₁ t₂ : Term x y)
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

module Builder where
  open Generic

-- private
--   module Example where
--     example : {x y z w : X}
--               (f : hom x y)
--               (g : hom y z)
--               (h : hom z w)
--             → (h ∘ g ∘ f) ⁻¹ ≡ f ⁻¹ ∘ g ⁻¹ ∘ h ⁻¹
--     example {x}{y}{z}{w} f g h = solve t₁ t₂ refl
--       where
--         t₁ : Term w x
--         t₁ = inv (var (suc (suc zero)) * var (suc zero) * var zero)
-- 
--         t₂ : Term w x
--         t₂ = inv (var zero) * inv (var (suc zero)) * inv (var (suc (suc zero)))
