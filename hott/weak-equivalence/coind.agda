{-# OPTIONS --without-K #-}
module hott.weak-equivalence.coind where

open import level
open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.isomorphism
open import container.m

data _~_ {i}{j}(X : Set i)(Y : Set j) : Set (i ⊔ j) where
  ~-intro : (f : X → Y)
          → (g : Y → X)
          → ((x : X)(y : Y) → ∞ ((f x ≡ y) ~ (x ≡ g y)))
          → (X ~ Y)

apply~ : ∀ {i j}{X : Set i}{Y : Set j} → X ~ Y → X → Y
apply~ (~-intro f _ _) = f

invert~ : ∀ {i j}{X : Set i}{Y : Set j} → X ~ Y → Y → X
invert~ (~-intro _ g _) = g

~⇒≅ : ∀ {i j}{X : Set i}{Y : Set j}
    → X ~ Y → X ≅ Y
~⇒≅ {X = X}{Y = Y}(~-intro f g φ) = record
  { to = f
  ; from = g
  ; iso₁ = λ x → sym (apply~ (♭ (φ x (f x))) refl)
  ; iso₂ = λ y → invert~ (♭ (φ (g y) y)) refl }

≅⇒~ : ∀ {i j}{X : Set i}{Y : Set j}
    → X ≅ Y → X ~ Y
≅⇒~ {X = X}{Y = Y} isom with ≅⇒≅' isom
... | (iso f g α β , δ) = ~-intro f g (λ x y → ♯ (≅⇒~ (φ x y)))
  where
    open ≡-Reasoning

    δ' = co-coherence (iso f g α β) δ

    iso₁ : {x : X}{y : Y}(p : f x ≡ y)
         → cong f (sym (α x) ⊚ cong g p) ⊚ β y ≡ p
    iso₁ {x} .{f x} refl = begin
        cong f (sym (α x) ⊚ refl) ⊚ β (f x)
      ≡⟨ cong (λ z → cong f z ⊚ β (f x)) (left-unit (sym (α x)))  ⟩
        cong f (sym (α x)) ⊚ β (f x)
      ≡⟨ cong (λ z → z ⊚ β (f x)) (cong-inv f (α x)) ⟩
        sym (cong f (α x)) ⊚ β (f x)
      ≡⟨ cong (λ z → sym z ⊚ β (f x)) (δ x) ⟩
        sym (β (f x)) ⊚ β (f x)
      ≡⟨ right-inverse (β (f x)) ⟩
        refl
      ∎

    iso₂' : {x : X}{y : Y}(q : g y ≡ x)
         → sym (α x) ⊚ cong g (cong f (sym q) ⊚ β y) ≡ sym q
    iso₂' .{g y}{y} refl = begin
        sym (α (g y)) ⊚ cong g (refl ⊚ β y)
      ≡⟨ cong (λ z → sym (α (g y)) ⊚ cong g z) (right-unit (β y)) ⟩
        sym (α (g y)) ⊚ cong g (β y)
      ≡⟨ cong (λ z → sym (α (g y)) ⊚ z) (δ' y) ⟩
        sym (α (g y)) ⊚ α (g y)
      ≡⟨ right-inverse (α (g y)) ⟩
        refl
      ∎

    iso₂ : {x : X}{y : Y}(q : x ≡ g y)
         → sym (α x) ⊚ cong g (cong f q ⊚ β y) ≡ q
    iso₂ {x}{y} q =
      subst (λ z → sym (α x) ⊚ cong g (cong f z ⊚ β y) ≡ z)
            (double-inverse q)
            (iso₂' (sym q))

    φ : (x : X)(y : Y) → (f x ≡ y) ≅ (x ≡ g y)
    φ x y = record
      { to = λ p → sym (α x) ⊚ cong g p
      ; from = λ q → cong f q ⊚ β y
      ; iso₁ = iso₁
      ; iso₂ = iso₂ }
