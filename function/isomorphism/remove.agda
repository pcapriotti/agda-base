{-# OPTIONS --without-K  #-}
module function.isomorphism.remove where

open import sum
open import equality
open import function.isomorphism.core
open import function.isomorphism.utils
open import function.isomorphism.properties
open import sets.empty

_minus_ : (A : Set) → A → Set
A minus x = Σ A λ x' → ¬ (x' ≡ x)

iso-remove : {A : Set}{B : Set}
           → (isom : A ≅ B)
           → (x : A)
           → (A minus x)
           ≅ (B minus (apply≅ isom x))
iso-remove {A = A}{B} isom x =
  Σ-ap-iso isom λ a
   → Π-ap-iso (iso≡ isom) λ _
   → refl≅
