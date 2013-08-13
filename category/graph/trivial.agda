{-# OPTIONS --without-K #-}

module category.graph.trivial where

open import level
open import sum
open import equality.core
open import function.core
open import function.isomorphism
open import category.graph.core
open import category.graph.morphism
open import sets.unit
open import overloading
open import hott.hlevel

trivial-graph : ∀ {i}(X : Set i) → Graph lzero i
trivial-graph X = mk-graph record
  { obj = ⊤
  ; hom = λ _ _ → X }

trivial-morphism : ∀ {i j}{X : Set i}{Y : Set j}
                 → (f : X → Y)
                 → Morphism (trivial-graph X) (trivial-graph Y)
trivial-morphism f = mk-morphism record
  { apply = id ; map = f }

trivial-morphism-equality : ∀ {i j}{X : Set i}{Y : Set j}
                            {f g : X → Y}
                          → (trivial-morphism f ≡ trivial-morphism g)
                          ≅ (f ≡ g)
trivial-morphism-equality {X = X}{Y = Y}{f = f}{g = g} = begin
    trivial-morphism f ≡ trivial-morphism g
  ≅⟨ iso≡ (sym≅ morphism-structure-iso) ⟩
    (id , invert is-mor-iso f) ≡ (id , invert is-mor-iso g)
  ≅⟨ sym≅ Σ-split-iso ⟩
    ( Σ (id ≡ id) λ p
    → subst IsMorphism p (invert is-mor-iso f)
    ≡ invert is-mor-iso g )
  ≅⟨ Σ-ap-iso lem (λ _ → refl≅) ⟩
    (⊤ × (invert is-mor-iso f ≡ invert is-mor-iso g))
  ≅⟨ ×-left-unit ⟩
    invert is-mor-iso f ≡ invert is-mor-iso g
  ≅⟨ iso≡ is-mor-iso ⟩
    f ≡ g
  ∎
  where
    open ≅-Reasoning

    lem : (id ≡ id) ≅ ⊤
    lem = begin
        id ≡ id
      ≅⟨ iso≡ Π-left-unit ⟩
        tt ≡ tt
      ≅⟨ contr-⊤-iso (h↑ ⊤-contr tt tt) ⟩
        ⊤
      ∎

    is-mor-iso : IsMorphism {W = trivial-graph X}{U = trivial-graph Y} id ≅ (X → Y)
    is-mor-iso = record
      { to = λ m → IsMorphism.map m
      ; from = λ h → record { map = h }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }
