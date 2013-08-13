{-# OPTIONS --without-K #-}

open import category.category

module category.product.properties {i₁ j₁ i₂ j₂}
                                    {C : Category i₁ j₁}
                                    {D : Category i₂ j₂} where
open import sum
open import equality.core
open import function.core
open import function.overloading
open import category.functor
open import category.graph
open import category.product.core

open as-category C
open as-category D

cat-proj₁ : Functor (C ⊗ D) C
cat-proj₁ = mk-functor {C = C ⊗ D}{D = C} record
  { apply = proj₁
  ; map = proj₁
  ; map-id = λ _ → refl
  ; map-hom = λ _ _ → refl }

cat-proj₂ : Functor (C ⊗ D) D
cat-proj₂ = mk-functor {C = C ⊗ D}{D = D} record
  { apply = λ { (_ , Y) → Y }
  ; map = λ { (_ , g) → g }
  ; map-id = λ _ → refl
  ; map-hom = λ _ _ → refl }

⟨_,_⟩ : ∀ {i₂ j₂} {E : Category i₂ j₂}
     → Functor E C → Functor E D
     → Functor E (C ⊗ D)
⟨_,_⟩ {E = E} F G = mk-functor {C = E}{D = C ⊗ D} record
  { apply = λ X → apply F X , apply G X
  ; map = λ f → map F f , map G f
  ; map-id = λ _ → ap₂ _,_ (map-id F _) (map-id G _)
  ; map-hom = λ f g → ap₂ _,_ (map-hom F _ _) (map-hom G _ _) }

cat-section₁ : obj D → Functor C (C ⊗ D)
cat-section₁ Y = mk-functor {C = C}{D = C ⊗ D} record
  { apply = λ X → X , Y
  ; map = λ f → f , id
  ; map-id = λ _ → refl
  ; map-hom = λ _ _ → ap₂ _,_ refl (sym (left-id _)) }

cat-section₂ : obj C → Functor D (C ⊗ D)
cat-section₂ X = mk-functor {C = D}{D = C ⊗ D} record
  { apply = λ Y → X , Y
  ; map = λ g → id , g
  ; map-id = λ _ → refl
  ; map-hom = λ _ _ → ap₂ _,_ (sym (left-id _)) refl }
