{-# OPTIONS --without-K #-}
module higher.circle.properties where

open import sum
open import equality
open import function.isomorphism
open import sets.empty
open import sets.bool
open import hott.equivalence
open import hott.univalence
open import higher.circle.core

non-simply-connected : ¬ (loop ≡ refl)
non-simply-connected loop-trivial = inv-non-trivial inv-trivial
  where
    not-iso : Bool ≅' Bool
    not-iso = iso not not H H , γ
      where
        H : (x : Bool) → not (not x) ≡ x
        H true = refl
        H false = refl

        γ : (x : Bool) → ap not (H x) ≡ H (not x)
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
          ≡⟨ ap (λ g → g true)
                  (sym (uni-coherence not-equiv)) ⟩
            coerce inv true
          ≡⟨ ap (λ z → coerce z true) q ⟩
            coerce refl true
          ≡⟨ refl ⟩
            true
          ∎

    f : S¹ → Set
    f = elim Bool inv

    f' : base ≡ base → Bool ≡ Bool
    f' p = ap f p

    β₂ : f' loop ≡ inv
    β₂ = β-loop Bool inv

    inv-trivial : inv ≡ refl
    inv-trivial = begin
        inv
      ≡⟨ sym β₂ ⟩
        f' loop
      ≡⟨ ap f' loop-trivial ⟩
        refl
      ∎
      where
        open ≡-Reasoning
