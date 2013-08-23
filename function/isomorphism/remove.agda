{-# OPTIONS --without-K  #-}
module function.isomorphism.remove where

open import sum
open import equality
open import function.isomorphism.core
open import function.isomorphism.utils
open import function.isomorphism.properties
open import function.overloading
open import sets.empty

_minus_ : ∀ {i}(A : Set i) → A → Set i
A minus x = Σ A λ x' → ¬ (x' ≡ x)

iso-remove : ∀ {i j}{A : Set i}{B : Set j}
           → (isom : A ≅ B)
           → (x : A)
           → (A minus x)
           ≅ (B minus (apply isom x))
iso-remove {A = A}{B} isom x =
  Σ-ap-iso isom λ a
   → Π-ap-iso (iso≡ isom) λ _
   → refl≅
