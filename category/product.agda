{-# OPTIONS --without-K #-}
module category.product where

open import level
open import sum
open import equality.core
open import category.structure
open import category.graph
open import category.category
open import category.functor
open import hott.hlevel

-- product of categories
-- for products *in* a category, see category.limit

open Category using (trunc)

_⊗_ : ∀ {i j i' j'}
    → Category i j → Category i' j'
    → Category (i ⊔ i') (j ⊔ j')
C ⊗ D = record
  { obj = obj C × obj D
  ; is-cat = record
    { is-gph = record
      { hom = λ { (X , Y) (X' , Y')
            → hom C X X' × hom D Y Y' } }
    ; id = λ { (X , Y) → id , id }
    ; _∘_ = λ { (f , g) (f' , g') → (f ∘ f' , g ∘ g') }
    ; left-unit = λ { _ →
        cong₂ _,_ (left-unit _)  (left-unit _) }
    ; right-unit = λ { _ →
        cong₂ _,_ (right-unit _)  (right-unit _) }
    ; associativity = λ { _ _ _ →
        cong₂ _,_ (associativity _ _ _) (associativity _ _ _) } }
  ; trunc = λ _ _ → ×-hlevel (trunc C _ _) (trunc D _ _) }
  where
    open cat-interface C
    open cat-interface D

private
  module Properties {i₀ j₀ i₁ j₁}
                    (C : Category i₀ j₀)
                    (D : Category i₁ j₁) where
    open Functor
    open cat-interface C
    open cat-interface D

    cat-proj₁ : Functor (C ⊗ D) C
    cat-proj₁ = record
      { morph = record
        { apply = proj₁
        ; map = proj₁ }
      ; is-func = record
        { map-id = λ _ → refl
        ; map-hom = λ _ _ → refl } }

    cat-proj₂ : Functor (C ⊗ D) D
    cat-proj₂ = record
      { morph = record
        { apply = proj₂
        ; map = proj₂ }
      ; is-func = record
        { map-id = λ _ → refl
        ; map-hom = λ _ _ → refl } }

    ⟨_,_⟩ : ∀ {i₂ j₂} {E : Category i₂ j₂}
         → Functor E C → Functor E D
         → Functor E (C ⊗ D)
    ⟨ F , G ⟩ = record
      { morph = record
        { apply = λ X → apply F X , apply G X
        ; map = λ f → map F f , map G f }
      ; is-func = record
        { map-id = λ _ → cong₂ _,_ (map-id F _) (map-id G _)
        ; map-hom = λ f g → cong₂ _,_ (map-hom F _ _) (map-hom G _ _) } }

    cat-section₁ : obj D → Functor C (C ⊗ D)
    cat-section₁ Y = record
      { morph = record
        { apply = λ X → X , Y
        ; map = λ f → f , id }
      ; is-func = record
        { map-id = λ _ → refl
        ; map-hom = λ _ _ → cong₂ _,_ refl (sym (left-unit _)) } }

    cat-section₂ : obj C → Functor D (C ⊗ D)
    cat-section₂ X = record
      { morph = record
        { apply = λ Y → X , Y
        ; map = λ g → id , g }
      ; is-func = record
        { map-id = λ _ → refl
        ; map-hom = λ _ _ → cong₂ _,_ (sym (left-unit _)) refl } }

open Properties public
