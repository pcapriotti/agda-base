{-# OPTIONS --without-K #-}
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

postulate
  S¹ : Set
  base : S¹
  loop : base ≡ base

private
  module Eliminators' {i}(B : S¹ → Set i)
                      (m : B base)
                      (l : subst B loop m ≡ m) where

    postulate
      elim' : (x : S¹) → B x
      β-base' : elim' base ≡ m
      β-loop' : cong (subst B loop) (sym β-base')
              ⊚ cong' elim' loop
              ⊚ β-base' ≡ l

private
  module Eliminators {i} {B : Set i}
                     (m : B) (l : m ≡ m) where
    open Eliminators' (λ _ → B) m (subst-const loop m ⊚ l)

    elim : S¹ → B
    elim = elim'

    β-base : elim base ≡ m
    β-base = β-base'

    β-loop : sym β-base
           ⊚ cong elim loop
           ⊚ β-base ≡ l
    β-loop = begin
        sym β-base ⊚ cong elim loop ⊚ β-base
      ≡⟨ lem β-base β-base loop ⟩
        sym (subst-const loop m) ⊚
        cong (subst (λ _ → B) loop) (sym β-base) ⊚
        cong' elim' loop ⊚ β-base
      ≡⟨ associativity (sym (subst-const loop m) ⊚ _) _ _ ⟩
        sym (subst-const loop m) ⊚
        cong (subst (λ _ → B) loop) (sym β-base) ⊚
        (cong' elim' loop ⊚ β-base)
      ≡⟨ associativity (sym (subst-const loop m)) _ _ ⟩
        sym (subst-const loop m) ⊚
        (cong (subst (λ _ → B) loop) (sym β-base) ⊚
        (cong' elim' loop ⊚ β-base))
      ≡⟨ cong (λ z → sym (subst-const loop m) ⊚ z)
          (sym (associativity
            (cong (subst (λ _ → B) loop) (sym β-base)) _ _)) ⟩
        sym (subst-const loop m) ⊚
        (cong (subst (λ _ → B) loop) (sym β-base) ⊚
         cong' elim' loop ⊚ β-base)
      ≡⟨ cong (λ z → sym (subst-const loop m) ⊚ z) β-loop' ⟩
        sym (subst-const loop m) ⊚ (subst-const loop m ⊚ l)
      ≡⟨ sym (associativity (sym (subst-const loop m))
                            (subst-const loop m) l) ⟩
        sym (subst-const loop m) ⊚ subst-const loop m ⊚ l
      ≡⟨ cong (λ z → z ⊚ l)
              (right-inverse (subst-const loop m)) ⟩
        l
      ∎
      where
        open ≡-Reasoning
        lem : {x y : S¹}
              (p₁ : elim x ≡ m)
              (p₂ : elim y ≡ m)
              (p : x ≡ y)
            → sym p₁ ⊚ cong elim p ⊚ p₂
            ≡ sym (subst-const p m)
            ⊚ cong (subst (λ _ → B) p) (sym p₁)
            ⊚ cong' elim' p ⊚ p₂
        lem p₁ p₂ refl =
          cong (λ z → z ⊚ refl ⊚ p₂) (sym (cong-id (sym p₁)))

open Eliminators public
open Eliminators' public

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

    not-is-equiv : weak-equiv not
    not-is-equiv = proj₂ (≅'⇒≈ not-iso)

    -- this extra step ensures that not-is-equiv is not 
    -- normalized, as that makes type checking extremely
    -- slow
    go : weak-equiv not → ¬ (loop ≡ refl)
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