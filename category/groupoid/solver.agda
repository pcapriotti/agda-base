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

eval : {x y : obj} → Term x y → hom x y
eval null = id _
eval (var f) = f
eval (g * f) = (eval g) ∘ (eval f)
eval (inv f) = eval f ⁻¹

invert : {x y : obj} → Term x y → Term y x
invert null = null
invert (var f) = inv (var f)
invert (g * f) = invert f * invert g
invert (inv f) = f

invert-correct : {x y : obj}(t : Term x y)
               → eval (invert t) ≡ eval t ⁻¹
invert-correct null = id-inverse G _
invert-correct (var f) = refl
invert-correct (g * f) = begin
    eval (invert (g * f))
  ≡⟨ cong₂ _∘_ (invert-correct f) (invert-correct g)  ⟩
    (eval f) ⁻¹ ∘ (eval g) ⁻¹
  ≡⟨ sym (inverse-comp G (eval f) (eval g)) ⟩
    eval (g * f) ⁻¹
  ∎
invert-correct (inv f) = sym (double-inverse G (eval f))

record Simplifier : Set (i ⊔ j) where
  constructor simplifier
  field
    simplify : {x y : obj} → Term x y → Term x y
    correctness : {x y : obj}(t : Term x y)
                → eval (simplify t) ≡ eval t
open Simplifier

combine : Simplifier → Simplifier → Simplifier
combine s₁ s₂ = simplifier simpl corr
  where
    simpl : {x y : obj} → Term x y → Term x y
    simpl t = simplify s₂ (simplify s₁ t)

    corr : {x y : obj}(t : Term x y)
         → eval (simpl t) ≡ eval t
    corr t = begin
        eval (simplify s₂ (simplify s₁ t))
      ≡⟨ correctness s₂ (simplify s₁ t) ⟩
        eval (simplify s₁ t)
      ≡⟨ correctness s₁ t ⟩
        eval t
      ∎

expand-inv : Simplifier
expand-inv = simplifier simpl corr
  where
    simpl : {x y : obj} → Term x y → Term x y
    simpl null = null
    simpl (var f) = var f
    simpl (g * f) = simpl g * simpl f
    simpl (inv f) = invert (simpl f)

    corr : {x y : obj} (t : Term x y)
                     → eval (simpl t) ≡ eval t
    corr null = refl
    corr (var f) = refl
    corr (g * f) =
      cong₂ _∘_ (corr g) (corr f)
    corr (inv f) = begin
        eval (simpl (inv f))
      ≡⟨ invert-correct (simpl f) ⟩
        eval (simpl f) ⁻¹
      ≡⟨ cong _⁻¹ (corr f) ⟩
        eval f ⁻¹
      ∎

solve₁ : {x y : obj} (s : Simplifier) (t₁ t₂ : Term x y)
       → simplify s t₁ ≡ simplify s t₂
       → eval t₁ ≡ eval t₂
solve₁ s t₁ t₂ p = begin
    eval t₁
  ≡⟨ sym (correctness s t₁) ⟩
    eval (simplify s t₁)
  ≡⟨ cong eval p ⟩
    eval (simplify s t₂)
  ≡⟨ correctness s t₂ ⟩
    eval t₂
  ∎

example : {x y z w : obj}
          (f : hom x y)
          (g : hom y z)
          (h : hom z w)
        → (h ∘ g ∘ f) ⁻¹ ≡ f ⁻¹ ∘ (g ⁻¹ ∘ h ⁻¹)
example {x}{y}{z}{w} f g h = solve₁ expand-inv t₁ t₂ refl
  where
    t₁ : Term w x
    t₁ = inv (var h * var g * var f)

    t₂ : Term w x
    t₂ = inv (var f) * (inv (var g) * inv (var h))
