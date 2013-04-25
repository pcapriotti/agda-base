{-# OPTIONS --without-K #-}

module category.graph.hlevel where

open import sum
open import equality.core
open import category.structure
open import category.graph.core
open import category.graph.morphism
open import function.isomorphism
open import sets.nat
open import hott.hlevel

private
  module Properties {i j i' j'}
                    {A : Graph i j}
                    {B : Graph i' j'} where

    morphism-structure-iso : Morphism A B
                           ≅ Σ (obj A → obj B)
                               (IsMorphism {A = A} {B = B})
    morphism-structure-iso = record
      { to = λ {(morphism f m) → f , m }
      ; from = λ {(f , m) → morphism f m }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }

    morph-hlevel : {n : ℕ}
                 → h n (obj B)
                 → (∀ x y → h n (hom B x y))
                 → h n (Morphism A B)
    morph-hlevel hB hB' = iso-hlevel (sym≅ morphism-structure-iso)
      (Σ-hlevel (Π-hlevel (λ _ → hB))
                (λ f → Π-hlevel-impl λ x
                     → Π-hlevel-impl λ y
                     → Π-hlevel λ _
                     → hB' (f x) (f y)))
      where
        isom : Morphism A B ≅ Σ (obj A → obj B) (IsMorphism {A = A} {B = B})
        isom = record
          { to = λ {(morphism f m) → f , m }
          ; from = λ {(f , m) → morphism f m }
          ; iso₁ = λ _ → refl
          ; iso₂ = λ _ → refl }
open Properties public
