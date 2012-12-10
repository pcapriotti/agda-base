{-# OPTIONS --without-K #-}
module equality.solver {i}(X : Set i) where

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
Graph k = X → X → Set k

TEnv : ∀ n → Set i
TEnv n = Vec (X × X) n

source : ∀ {n} → TEnv n → Fin n → X
source tenv i = proj₁ (tenv ! i)

target : ∀ {n} → TEnv n → Fin n → X
target tenv i = proj₂ (tenv ! i)

Env : ∀ {n} → TEnv n → Set _
Env {n} tenv = (i : Fin n) → source tenv i ≡ target tenv i

module Generic {n : ℕ} (tenv : TEnv n) where
  data Term : Graph i where
    null : ∀ {x} → Term x x
    var : (i : Fin n) → Term (source tenv i) (target tenv i)
    _*_ : ∀ {x y z} → Term y z → Term x y → Term x z
    inv : ∀ {x y} → Term y x → Term x y
  infixl 5 _*_

  module WithEnv (env : Env tenv) where
    evalT : {x y : X} → Term x y → x ≡ y
    evalT null = refl
    evalT (var x) = env x
    evalT (g * f) = evalT f ⊚ evalT g
    evalT (inv t) = evalT t ⁻¹

    data List : X → X → Set i where
      nil : ∀ {x} → List x x
      _∷_ : ∀ {x y z} → y ≡ z → List x y → List x z
      _∺_ : ∀ {x y z} → z ≡ y → List x y → List x z
    infixr 5 _∷_ _∺_

    evalL : {x y : X} → List x y → x ≡ y
    evalL nil = refl
    evalL (f ∷ fs) = evalL fs ⊚ f
    evalL (f ∺ fs) = evalL fs ⊚ f ⁻¹

    _++_ : ∀ {x y z} → List y z → List x y → List x z
    nil ++ gs = gs
    (f ∷ fs) ++ gs = f ∷ (fs ++ gs)
    (f ∺ fs) ++ gs = f ∺ (fs ++ gs)
    infixr 5 _++_

    oneL : ∀ {x y} (f : x ≡ y) → evalL (f ∷ nil) ≡ f
    oneL f = right-unit f

    invL : ∀ {x y} (f : x ≡ y) → evalL (f ∺ nil) ≡ f ⁻¹
    invL f = right-unit (f ⁻¹)

    eval++ : ∀ {x y z}(fs : List y z)(gs : List x y)
           → evalL (fs ++ gs) ≡ evalL gs ⊚ evalL fs
    eval++ nil gs = sym (left-unit (evalL gs))
    eval++ (f ∷ fs) gs = begin
        evalL (fs ++ gs) ⊚ f
      ≡⟨ cong (λ z → z ⊚ f) (eval++ fs gs) ⟩
        (evalL gs ⊚ evalL fs) ⊚ f
      ≡⟨ associativity (evalL gs) (evalL fs) f ⟩
        evalL gs ⊚ (evalL fs ⊚ f)
      ∎
    eval++ (f ∺ fs) gs = begin
        evalL (fs ++ gs) ⊚ f ⁻¹
      ≡⟨ cong (λ z → z ⊚ f ⁻¹) (eval++ fs gs) ⟩
        evalL gs ⊚ evalL fs ⊚ f ⁻¹
      ≡⟨ associativity (evalL gs) (evalL fs) (f ⁻¹) ⟩
        evalL gs ⊚ (evalL fs ⊚ f ⁻¹)
      ∎

    reverse : ∀ {x y} → List x y → List y x
    reverse nil = nil
    reverse (f ∷ fs) = reverse fs ++ (f ∺ nil)
    reverse (f ∺ fs) = reverse fs ++ (f ∷ nil)

    reverse-inv : ∀ {x y}(t : List x y)
                → evalL (reverse t) ≡ (evalL t) ⁻¹
    reverse-inv nil = refl
    reverse-inv (f ∷ fs) = begin
        evalL (reverse fs ++ (f ∺ nil))
      ≡⟨ eval++ (reverse fs) (f ∺ nil) ⟩
        evalL (f ∺ nil) ⊚ evalL (reverse fs)
      ≡⟨ cong₂ _⊚_ (invL f) (reverse-inv fs) ⟩
        f ⁻¹ ⊚ evalL fs ⁻¹
      ≡⟨ sym (inverse-comp (evalL fs) f) ⟩
        (evalL fs ⊚ f) ⁻¹
      ∎
    reverse-inv (f ∺ fs) = begin
        evalL (reverse fs ++ (f ∷ nil))
      ≡⟨ eval++ (reverse fs) (f ∷ nil) ⟩
        evalL (f ∷ nil) ⊚ evalL (reverse fs)
      ≡⟨ cong₂ _⊚_ (oneL f) (reverse-inv fs) ⟩
        f ⊚ evalL fs ⁻¹
      ≡⟨ cong (λ z → z ⊚ evalL fs ⁻¹) (sym (double-inverse f)) ⟩
        (f ⁻¹) ⁻¹ ⊚ evalL fs ⁻¹
      ≡⟨ sym (inverse-comp (evalL fs) (f ⁻¹)) ⟩
        (evalL fs ⊚ f ⁻¹) ⁻¹
      ∎

    linearize : {x y : X} → Term x y → List x y
    linearize null = nil
    linearize (var f) = env f ∷ nil
    linearize (g * f) = linearize g ++ linearize f
    linearize (inv f) = reverse (linearize f)

    linearize-correct : {x y : X}(t : Term x y)
                      → evalL (linearize t) ≡ evalT t
    linearize-correct null = refl
    linearize-correct (var f) = right-unit (env f)
    linearize-correct (g * f) = begin
        evalL (linearize g ++ linearize f)
      ≡⟨ eval++ (linearize g) (linearize f) ⟩
        evalL (linearize f) ⊚ evalL (linearize g)
      ≡⟨ cong₂ _⊚_ (linearize-correct f) (linearize-correct g) ⟩
        evalT f ⊚ evalT g
      ∎
    linearize-correct (inv t) = begin
        evalL (reverse (linearize t))
      ≡⟨ reverse-inv (linearize t) ⟩
        evalL (linearize t) ⁻¹
      ≡⟨ cong (_⁻¹) (linearize-correct t) ⟩
        evalT (inv t)
      ∎

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
