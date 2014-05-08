{-# OPTIONS --without-K --type-in-type #-}
module higher.circle where

open import sum using (_,_ ; proj₂)
open import function using (id)
open import sets.empty
open import sets.bool
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.isomorphism.coherent
open import hott.weak-equivalence
open import hott.univalence
open import function.isomorphism using (iso)

data S¹ : Set where
  base : S¹

postulate loop : base ≡ base

private
  module Eliminators' (B : S¹ → Set)
                      (m : B base)
                      (l : subst B loop m ≡ m) where
    elim' : (x : S¹) → B x
    elim' base = m

    β-base' : elim' base ≡ m
    β-base' = refl

    postulate β-loop' : cong' elim' loop ≡ l

private
  module Eliminators {B : Set}
                     (m : B) (l : m ≡ m) where
    open Eliminators' (λ _ → B) m (subst-const loop m ⊚ l)

    elim : S¹ → B
    elim = elim'

    β-base : elim base ≡ m
    β-base = refl

    postulate β-loop : cong elim loop ≡ l

open Eliminators public
open Eliminators' public

non-simply-connected : ¬ (loop ≡ refl)
non-simply-connected loop-trivial = inv-non-trivial inv-trivial
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

    abstract
      not-is-equiv : weak-equiv not
      not-is-equiv = proj₂ (≅'⇒≈ not-iso)

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

    f' : base ≡ base → Bool ≡ Bool
    f' p = cong f p

    β₂ : f' loop ≡ inv
    β₂ = β-loop Bool inv

    inv-trivial : inv ≡ refl
    inv-trivial = begin
        inv
      ≡⟨ sym β₂ ⟩
        f' loop
      ≡⟨ cong f' loop-trivial ⟩
        refl
      ∎
      where
        open ≡-Reasoning
