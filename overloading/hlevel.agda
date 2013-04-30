{-# OPTIONS --without-K #-}

module overloading.hlevel where

open import sum
open import equality.core
open import overloading.bundle
open import function.isomorphism
open import hott.hlevel.core
open import sets.unit

open Bundle

bundle-structure-iso : ∀ {i j}{Base : Set i}
                       (Struct : Base → Set j)
                     → Σ Base Struct ≅ Bundle Struct
bundle-structure-iso Struct = record
  { to = λ { (X , s) → bundle X s }
  ; from = λ { (bundle X s) → X , s }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

bundle-equality-iso : ∀ {i j}{Base : Set i}
                      (Struct : Base → Set j)
                    → ((B : Base) → h 1 (Struct B))
                    → {X Y : Bundle Struct}
                    → (parent X ≡ parent Y)
                    ≅ (X ≡ Y)
bundle-equality-iso Struct hS {X}{Y} = begin
    parent X ≡ parent Y
  ≅⟨ sym≅ ×-right-unit ⟩
    ((parent X ≡ parent Y) × ⊤)
  ≅⟨ Σ-cong-iso refl≅ (λ p → sym≅ (contr-⊤-iso (hS _ _ _))) ⟩
    ( Σ (parent X ≡ parent Y) λ p
    → (subst Struct p (struct X) ≡ struct Y) )
  ≅⟨ Σ-split-iso ⟩
    (parent X , struct X) ≡ (parent Y , struct Y)
  ≅⟨ iso≡ (bundle-structure-iso Struct) ⟩
    X ≡ Y
  ∎
  where open ≅-Reasoning
