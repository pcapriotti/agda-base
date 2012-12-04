{-# OPTIONS --without-K #-}

module category.groupoid.properties where

open import category.category
open import category.groupoid
open import category.functor hiding (id)
open import equality.core using (_≡_ ; sym ; cong)
open import equality.reasoning

private
  module Properties {i j}(G : Groupoid i j) where
    open Groupoid G
    open ≡-Reasoning

    unique-inverse : {x y : obj} (p : hom x y)(q : hom y x) → p ⊚ q ≡ id x → q ≡ p ⁻¹
    unique-inverse {x}{y} p q eq = begin
      q
                   ≡⟨ sym (right-unit q) ⟩
      id y ⊚ q
                   ≡⟨ cong (λ a → a ⊚ q) (sym (right-inverse p)) ⟩
      p ⁻¹ ⊚ p ⊚ q
                   ≡⟨ sym (associativity (p ⁻¹) p q) ⟩
      p ⁻¹ ⊚ (p ⊚ q)
                   ≡⟨ cong (_⊚_ (p ⁻¹)) eq ⟩
      p ⁻¹ ⊚ id x
                   ≡⟨ left-unit (p ⁻¹) ⟩
      p ⁻¹
                   ∎

    double-inverse : {x y : obj} (p : hom x y) → (p ⁻¹) ⁻¹ ≡ p
    double-inverse p = sym (unique-inverse (p ⁻¹) p (right-inverse p))

    inverse-comp : {x y z : obj} (p : hom x y) (q : hom y z)
                 → (p ⊚ q) ⁻¹ ≡ q ⁻¹ ⊚ p ⁻¹
    inverse-comp p q = sym (unique-inverse (p ⊚ q) (q ⁻¹ ⊚ p ⁻¹) lem)
      where
        lem : (p ⊚ q) ⊚ (q ⁻¹ ⊚ p ⁻¹) ≡ id _
        lem = begin
            p ⊚ q ⊚ (q ⁻¹ ⊚ p ⁻¹)
          ≡⟨ associativity (p ⊚ q) (q ⁻¹) (p ⁻¹) ⟩
            p ⊚ q ⊚ q ⁻¹ ⊚ p ⁻¹
          ≡⟨ cong (λ a → a ⊚ p ⁻¹) (sym (associativity p q (q ⁻¹))) ⟩
            p ⊚ (q ⊚ q ⁻¹) ⊚ p ⁻¹
          ≡⟨ cong (λ a → p ⊚ a ⊚ p ⁻¹) (left-inverse q) ⟩
            p ⊚ id _ ⊚ p ⁻¹
          ≡⟨ cong (λ a → a ⊚ p ⁻¹) (left-unit p) ⟩
            p ⊚ p ⁻¹
          ≡⟨ left-inverse p ⟩
            id _
          ∎

  module Properties₂ {i j i' j'}{G : Groupoid i j}{H : Groupoid i' j'}
                     (F : Morphism G H) where
    open Properties
    open Groupoid hiding (_⊚_ ; _⁻¹)
    open Groupoid G using () renaming (_⊚_ to _⊚₁_ ; _⁻¹ to inv₁)
    open Groupoid H using () renaming (_⊚_ to _⊚₂_ ; _⁻¹ to inv₂)
    open Functor F

    map-inv : {x y : obj G}
              (f : hom G x y)
            → map (inv₁ f) ≡ inv₂ (map f)
    map-inv {x} f = unique-inverse H (map f) (map (inv₁ f)) lem
      where
        open equality.reasoning
        open ≡-Reasoning

        lem : map f ⊚₂ map (inv₁ f) ≡ id H _
        lem = begin
            map f ⊚₂ map (inv₁ f)
          ≡⟨ sym (map-hom f (inv₁ f)) ⟩
            map (f ⊚₁ inv₁ f)
          ≡⟨ cong map (left-inverse G f) ⟩
            map (id G _)
          ≡⟨ map-id _ ⟩
            id H _
          ∎

open Properties public
open Properties₂ public