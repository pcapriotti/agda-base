{-# OPTIONS --without-K #-}

open import category.groupoid

module category.groupoid.solver {i j}
       (G : Groupoid i j) where

open import level using (_⊔_)
open import equality.core
open import equality.reasoning
open import category.groupoid.properties

open Groupoid G hiding (_⊚_)
open ≡-Reasoning

data Term : obj → obj → Set (i ⊔ j) where
  null : ∀ {x} → Term x x
  var : ∀ {x y} → hom x y → Term x y
  _*_ : ∀ {x y z} → Term y z → Term x y → Term x z
  inv : ∀ {x y} → Term y x → Term x y
infixl 5 _*_

evalT : {x y : obj} → Term x y → hom x y
evalT null = id _
evalT (var f) = f
evalT (g * f) = (evalT g) ∘ (evalT f)
evalT (inv f) = evalT f ⁻¹

data List : obj → obj → Set (i ⊔ j) where
  nil : ∀ {x} → List x x
  _∷_ : ∀ {x y z} → hom y z → List x y → List x z
  _∺_ : ∀ {x y z} → hom z y → List x y → List x z
infixr 5 _∷_ _∺_

evalL : {x y : obj} → List x y → hom x y
evalL nil = id _
evalL (f ∷ fs) = f ∘ evalL fs
evalL (f ∺ fs) = f ⁻¹ ∘ evalL fs

_++_ : ∀ {x y z} → List y z → List x y → List x z
nil ++ gs = gs
(f ∷ fs) ++ gs = f ∷ (fs ++ gs)
(f ∺ fs) ++ gs = f ∺ (fs ++ gs)
infixr 5 _++_

oneL : ∀ {x y} (f : hom x y) → evalL (f ∷ nil) ≡ f
oneL f = right-unit f

invL : ∀ {x y} (f : hom x y) → evalL (f ∺ nil) ≡ f ⁻¹
invL f = right-unit (f ⁻¹)

eval++ : ∀ {x y z}(fs : List y z)(gs : List x y)
       → evalL (fs ++ gs) ≡ evalL fs ∘ evalL gs
eval++ nil gs = sym (left-unit (evalL gs))
eval++ (f ∷ fs) gs = begin
    f ∘ (evalL (fs ++ gs))
  ≡⟨ cong (_∘_ f) (eval++ fs gs) ⟩
    f ∘ (evalL fs ∘ evalL gs)
  ≡⟨ sym (associativity (evalL gs) (evalL fs) f) ⟩
    (f ∘ evalL fs) ∘ evalL gs
  ∎
eval++ (f ∺ fs) gs = begin
    f ⁻¹ ∘ (evalL (fs ++ gs))
  ≡⟨ cong (_∘_ (f ⁻¹)) (eval++ fs gs) ⟩
    f ⁻¹ ∘ (evalL fs ∘ evalL gs)
  ≡⟨ sym (associativity (evalL gs) (evalL fs) (f ⁻¹)) ⟩
    (f ⁻¹ ∘ evalL fs) ∘ evalL gs
  ∎

reverse : ∀ {x y} → List x y → List y x
reverse nil = nil
reverse (f ∷ fs) = reverse fs ++ (f ∺ nil)
reverse (f ∺ fs) = reverse fs ++ (f ∷ nil)

reverse-inv : ∀ {x y}(t : List x y)
            → evalL (reverse t) ≡ (evalL t) ⁻¹
reverse-inv nil = id-inverse G _
reverse-inv (f ∷ fs) = begin
    evalL (reverse fs ++ (f ∺ nil))
  ≡⟨ eval++ (reverse fs) (f ∺ nil) ⟩
    evalL (reverse fs) ∘ evalL (f ∺ nil)
  ≡⟨ cong₂ _∘_ (reverse-inv fs) (invL f) ⟩
    evalL fs ⁻¹ ∘ f ⁻¹
  ≡⟨ sym (inverse-comp G (evalL fs) f) ⟩
    (f ∘ evalL fs) ⁻¹
  ∎
reverse-inv (f ∺ fs) = begin
    evalL (reverse fs ++ (f ∷ nil))
  ≡⟨ eval++ (reverse fs) (f ∷ nil) ⟩
    evalL (reverse fs) ∘ evalL (f ∷ nil)
  ≡⟨ cong₂ _∘_ (reverse-inv fs) (oneL f) ⟩
    evalL fs ⁻¹ ∘ f
  ≡⟨ cong (_∘_ (evalL fs ⁻¹)) (sym (double-inverse G f)) ⟩
    evalL fs ⁻¹ ∘ (f ⁻¹) ⁻¹
  ≡⟨ sym (inverse-comp G (evalL fs) (f ⁻¹)) ⟩
    (f ⁻¹ ∘ evalL fs) ⁻¹
  ∎

linearize : {x y : obj} → Term x y → List x y
linearize null = nil
linearize (var f) = f ∷ nil
linearize (g * f) = linearize g ++ linearize f
linearize (inv f) = reverse (linearize f)

linearize-correct : {x y : obj}(t : Term x y)
                  → evalL (linearize t) ≡ evalT t
linearize-correct null = refl
linearize-correct (var f) = right-unit f
linearize-correct (g * f) = begin
    evalL (linearize g ++ linearize f)
  ≡⟨ eval++ (linearize g) (linearize f) ⟩
    evalL (linearize g) ∘ evalL (linearize f)
  ≡⟨ cong₂ _∘_ (linearize-correct g) (linearize-correct f) ⟩
    evalT g ∘ evalT f
  ∎
linearize-correct (inv t) = begin
    evalL (reverse (linearize t))
  ≡⟨ reverse-inv (linearize t) ⟩
    evalL (linearize t) ⁻¹
  ≡⟨ cong (_⁻¹) (linearize-correct t) ⟩
    evalT (inv t)
  ∎

solve : {x y : obj} (t₁ t₂ : Term x y)
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

example : {x y z w : obj}
          (f : hom x y)
          (g : hom y z)
          (h : hom z w)
        → (h ∘ g ∘ f) ⁻¹ ≡ f ⁻¹ ∘ g ⁻¹ ∘ h ⁻¹
example {x}{y}{z}{w} f g h = solve t₁ t₂ refl
  where
    t₁ : Term w x
    t₁ = inv (var h * var g * var f)

    t₂ : Term w x
    t₂ = inv (var f) * inv (var g) * inv (var h)
