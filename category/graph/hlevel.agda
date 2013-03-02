{-# OPTIONS --without-K #-}

module category.graph.hlevel where

open import sum
open import equality.core
open import category.graph.core
open import function.isomorphism
open import hott.hlevel

open Graph

morph-hlevel : ∀ {i j i' j' n}
               {A : Graph i j}
               {B : Graph i' j'}
             → h n (obj B)
             → (∀ x y → h n (hom B x y))
             → h n (Morphism A B)
morph-hlevel {A = A}{B = B} hB hB' = iso-hlevel (sym≅ isom)
  (Σ-hlevel (Π-hlevel (λ _ → hB))
            (λ f → Π-hlevel-impl λ x
                 → Π-hlevel-impl λ y
                 → Π-hlevel λ _
                 → hB' (f x) (f y)))
  where
    IsMorphism : (f : obj A → obj B) → Set _
    IsMorphism f = ∀ {x y} → hom A x y → hom B (f x) (f y)

    isom : Morphism A B ≅ Σ (obj A → obj B) IsMorphism
    isom = record
      { to = λ {(morphism f m) → f , m }
      ; from = λ {(f , m) → morphism f m }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }
