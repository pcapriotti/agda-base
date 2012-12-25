{-# OPTIONS --without-K #-}
module category.instances.set where

open import sum
open import equality using (refl)
open import function as f
open import function.extensionality
open import level using (lzero ; lsuc)
open import category.category
open import hott.hlevel
open import hott.univalence.properties

set : ∀ i → Category (lsuc i) i
set i = record
  { obj = HSet i
  ; hom = λ A B → (proj₁ A → proj₁ B)
  ; trunc = λ { _ (B , h2B)
              → Π-hlevel strong-ext 2 (λ _ → h2B) }
  ; id = λ A → f.id {A = proj₁ A}
  ; _∘_ = f._∘'_
  ; left-unit = λ f → refl
  ; right-unit = λ f → refl
  ; associativity = λ f g h → refl }