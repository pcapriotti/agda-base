{-# OPTIONS --without-K #-}
module category.product where

open import level
open import sum
open import equality.core
open import category.category
open import category.functor
  using (Functor; module Functor)
open import hott.hlevel

-- product of categories
-- for products *in* a category, see category.limit

open Category

_⊗_ : ∀ {i j i' j'}
    → Category i j → Category i' j'
    → Category (i ⊔ i') (j ⊔ j')
C ⊗ D = record
  { obj = obj C × obj D
  ; hom = λ { (X , Y) (X' , Y')
            → hom C X X' × hom D Y Y' }
  ; trunc = λ _ _ → ×-hlevel (trunc C _ _) (trunc D _ _)
  ; id = λ { (X , Y) → (id C X , id D Y) }
  ; _∘_ = λ { (f , g) (f' , g') → (f ⋆ f' , g ✦ g') }
  ; left-unit = λ { _ →
      cong₂ _,_ (left-unit C _)  (left-unit D _) }
  ; right-unit = λ { _ →
      cong₂ _,_ (right-unit C _)  (right-unit D _) }
  ; associativity = λ { _ _ _ →
      cong₂ _,_ (associativity C _ _ _) (associativity D _ _ _) }
  }
  where
    open Category C using ()
      renaming (_∘_ to _⋆_)
    open Category D using ()
      renaming (_∘_ to _✦_)

private
  module Properties {i₀ j₀ i₁ j₁}
                    (C : Category i₀ j₀)
                    (D : Category i₁ j₁) where
    open Functor

    cat-proj₁ : Functor (C ⊗ D) C
    cat-proj₁ = record
      { apply = proj₁
      ; map = proj₁
      ; map-id = λ _ → refl
      ; map-hom = λ _ _ → refl }

    cat-proj₂ : Functor (C ⊗ D) D
    cat-proj₂ = record
      { apply = proj₂
      ; map = proj₂
      ; map-id = λ _ → refl
      ; map-hom = λ _ _ → refl }

    ⟨_,_⟩ : ∀ {i₂ j₂} {E : Category i₂ j₂}
         → Functor E C → Functor E D
         → Functor E (C ⊗ D)
    ⟨ F , G ⟩ = record
      { apply = λ X → apply F X , apply G X
      ; map = λ f → map F f , map G f
      ; map-id = λ _ → cong₂ _,_ (map-id F _) (map-id G _)
      ; map-hom = λ f g → cong₂ _,_ (map-hom F _ _) (map-hom G _ _) }

    cat-section₁ : obj D → Functor C (C ⊗ D)
    cat-section₁ Y = record
      { apply = λ X → X , Y
      ; map = λ f → f , id D Y
      ; map-id = λ _ → refl
      ; map-hom = λ _ _ → cong₂ _,_ refl (sym (left-unit D _)) }

    cat-section₂ : obj C → Functor D (C ⊗ D)
    cat-section₂ X = record
      { apply = λ Y → X , Y
      ; map = λ g → id C X , g
      ; map-id = λ _ → refl
      ; map-hom = λ _ _ → cong₂ _,_ (sym (left-unit C _)) refl }

open Properties public
