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

simplify₁ : {x y : obj} → Term x y → Term x y
simplify₁ null = null
simplify₁ (var f) = var f
simplify₁ (g * f) = simplify₁ g * simplify₁ f
simplify₁ (inv f) = invert (simplify₁ f)

simplify₁-correct : {x y : obj} (t : Term x y)
                  → eval (simplify₁ t) ≡ eval t
simplify₁-correct null = refl
simplify₁-correct (var f) = refl
simplify₁-correct (g * f) =
  cong₂ _∘_ (simplify₁-correct g) (simplify₁-correct f)
simplify₁-correct (inv f) = begin
    eval (simplify₁ (inv f))
  ≡⟨ invert-correct (simplify₁ f) ⟩
    eval (simplify₁ f) ⁻¹
  ≡⟨ cong _⁻¹ (simplify₁-correct f) ⟩
    eval f ⁻¹
  ∎

solve₁ : {x y : obj} (t₁ t₂ : Term x y)
       → simplify₁ t₁ ≡ simplify₁ t₂
       → eval t₁ ≡ eval t₂
solve₁ t₁ t₂ p = begin
    eval t₁
  ≡⟨ sym (simplify₁-correct t₁) ⟩
    eval (simplify₁ t₁)
  ≡⟨ cong eval p ⟩
    eval (simplify₁ t₂)
  ≡⟨ simplify₁-correct t₂ ⟩
    eval t₂
  ∎

example : {x y z w : obj}
          (f : hom x y)
          (g : hom y z)
          (h : hom z w)
        → (h ∘ g ∘ f) ⁻¹ ≡ f ⁻¹ ∘ (g ⁻¹ ∘ h ⁻¹)
example {x}{y}{z}{w} f g h = solve₁ t₁ t₂ refl
  where
    t₁ : Term w x
    t₁ = inv (var h * var g * var f)

    t₂ : Term w x
    t₂ = inv (var f) * (inv (var g) * inv (var h))
