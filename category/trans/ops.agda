{-# OPTIONS --without-K #-}

open import category.category.core

module category.trans.ops (C D : Category) where

open import function.core
open import function.overloading
open import equality
open import category.category.zero
open import category.graph
open import category.functor.core
open import category.trans.core

open as-category C
open as-category D

private
  Id : (F : Functor C D) → Nat F F
  Id F = nt (λ X → id)
            ( λ f → left-id (map F f)
                  ⊚ right-id (map F f) ⁻¹ )

  Compose : {F G H : Functor C D} → Nat G H → Nat F G → Nat F H
  Compose {F}{G}{H} (nt α α-nat) (nt β β-nat) = (nt γ γ-nat)
    where
      open ≡-Reasoning

      γ : ∀ X → hom (apply F X) (apply H X)
      γ X = α X ∘ β X

      γ-nat : ∀ {X Y} (f : hom X Y)
            → γ Y ∘ map F f ≡ map H f ∘ γ X
      γ-nat {X}{Y} f = begin
          γ Y ∘ map F f
        ≡⟨ assoc _ _ _ ⟩
          α Y ∘ (β Y ∘ map F f)
        ≡⟨ cong (_∘_ (α Y)) (β-nat f) ⟩
          α Y ∘ (map G f ∘ β X)
        ≡⟨ sym (assoc _ _ _) ⟩
          (α Y ∘ map G f) ∘ β X
        ≡⟨ cong (λ z → z ∘ β X) (α-nat f) ⟩
          map H f ∘ α X ∘ β X
        ≡⟨ assoc _ _ _ ⟩
          map H f ∘ γ X
        ∎

-- functor category
Func₀ : Category₀
Func₀ = mk-category₀ record
  { obj = Functor C D
  ; hom = Nat
  ; id = Id
  ; _∘_ = Compose }
