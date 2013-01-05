{-# OPTIONS --without-K #-}

open import category.category

module category.mono {i j}(C : Category i j) where

open import category.isomorphism
open import equality.core
open import equality.reasoning
open import hott.hlevel

open Category C using (is-cat)

monic : ∀ {x y} (f : hom x y) → Set _
monic {x}{y} f = ∀ {z} (g h : hom z x)
                 → f ∘ g ≡ f ∘ h
                 → g ≡ h

monic-h1 : ∀ {x y}(f : hom x y)
           → h 1 (monic f)
monic-h1 f = Π-hlevel-impl λ z
           → Π-hlevel λ g
           → Π-hlevel λ f
           → Π-hlevel λ p
           → trunc C _ _ _ _

-- an isomorphism is monic
iso-monic : ∀ {x y} (isom : cat-iso C x y)
          → monic (cat-iso.to isom)
iso-monic {x}{y} (c-iso f g H K) a b p = begin
    a
  ≡⟨ sym (lem a) ⟩
    g ∘ (f ∘ a)
  ≡⟨ cong (λ c → g ∘ c) p ⟩
    g ∘ (f ∘ b)
  ≡⟨ lem b ⟩
    b
  ∎
  where
    open ≡-Reasoning

    lem : ∀ {z} → (c : hom z x)
        → g ∘ (f ∘ c) ≡ c
    lem c = begin
        g ∘ (f ∘ c)
      ≡⟨ sym (associativity c f g) ⟩
        g ∘ f ∘ c
      ≡⟨ cong (λ α → α ∘ c) H ⟩
        id _ ∘ c
      ≡⟨ left-unit c ⟩
        c
      ∎
