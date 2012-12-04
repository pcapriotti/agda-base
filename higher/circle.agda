{-# OPTIONS --without-K #-}
module higher.circle where

open import sum using (_,_ ; proj₂)
open import sets.empty
open import sets.bool
open import equality.core
open import equality.calculus
open import equality.reasoning
open import hott.coherence
open import hott.weak-equivalence
open import hott.univalence
open import function.isomorphism using (iso)

postulate
  S¹ : Set
  base : S¹
  loop : base ≡ base

  elim : ∀ {i} {X : Set i}
       → (m : X)
       → (m ≡ m)
       → S¹ → X

  β-base : ∀ {i} {X : Set i}
         → (m : X) (l : m ≡ m)
         → elim m l base ≡ m

  β-loop : ∀ {i} {X : Set i}
           → (m : X)
           → (l : m ≡ m)
           → sym (β-base m l) ⊚ cong (elim m l) loop ⊚ β-base m l ≡ l

module Dependent {i}(B : S¹ → Set i)
                 (m : B base)
                 (l : subst B loop m ≡ m) where

  postulate
    elim' : (x : S¹) → B x
    β-base' : elim' base ≡ m
open Dependent public

non-simply-connected : ¬ (loop ≡ refl)
non-simply-connected = go not-is-equiv
  where
    not-iso : Bool ≅' Bool
    not-iso = iso not not H H , γ
      where
        H : (x : Bool) → not (not x) ≡ x
        H true = refl
        H false = refl

        γ : (x : Bool) → cong not (H x) ≡ H (not x)
        γ true = refl
        γ false = refl

    not-is-equiv : isWeakEquiv not
    not-is-equiv = proj₂ (≅'⇒≈ not-iso)

    -- this extra step ensures that not-is-equiv is not 
    -- normalized, as that makes type checking extremely
    -- slow
    go : isWeakEquiv not → ¬ (loop ≡ refl)
    go not-is-equiv loop-trivial = inv-non-trivial inv-trivial
      where
        not-equiv : Bool ≈ Bool
        not-equiv = not , not-is-equiv

        inv : Bool ≡ Bool
        inv = ≈⇒≡ not-equiv

        inv-non-trivial : ¬ (inv ≡ refl)
        inv-non-trivial q = distinct absurd
          where
            open ≡-Reasoning

            distinct : false ≡ true → ⊥
            distinct ()

            absurd : false ≡ true
            absurd = begin
                false
              ≡⟨ refl ⟩
                not true
              ≡⟨ cong (λ g → g true)
                      (sym (uni-coherence not-equiv)) ⟩
                coerce inv true
              ≡⟨ cong (λ z → coerce z true) q ⟩
                coerce refl true
              ≡⟨ refl ⟩
                true
              ∎

        f : S¹ → Set
        f = elim Bool inv

        β₁ : f base ≡ Bool
        β₁ = β-base Bool inv 

        f' : base ≡ base → Bool ≡ Bool
        f' p = sym β₁ ⊚ cong f p ⊚ β₁

        β₂ : f' loop ≡ inv
        β₂ = β-loop Bool inv

        inv-trivial : inv ≡ refl
        inv-trivial = begin
            inv
          ≡⟨ sym β₂ ⟩
            f' loop
          ≡⟨ cong f' loop-trivial ⟩
            f' refl
          ≡⟨ refl ⟩
            sym β₁ ⊚ refl ⊚ β₁
          ≡⟨ cong (λ z → z ⊚ β₁)
                  (left-unit (sym β₁)) ⟩
            sym β₁ ⊚ β₁
          ≡⟨ right-inverse β₁ ⟩
            refl
          ∎
          where
            open ≡-Reasoning