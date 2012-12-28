{-# OPTIONS --without-K #-}
open import category.category

module category.isomorphism {i j}(C : Category i j) where

open import hott.hlevel.properties
open import hott.univalence.properties
open import function.isomorphism.properties
open import sum
open import equality.core using (_≡_ ; refl)
open import hott.hlevel

open Category C

record cat-iso (x y : obj) : Set j where
  constructor c-iso
  field
    to : hom x y
    from : hom y x

    iso₁ : from ∘ to ≡ id x
    iso₂ : to ∘ from ≡ id y

≡⇒iso : {x y : obj} → x ≡ y → cat-iso x y
≡⇒iso {x}{.x} refl = record
  { to = id x
  ; from = id x
  ; iso₁ = left-unit _
  ; iso₂ = left-unit _ }

cat-iso-hset : ∀ x y → h 2 (cat-iso x y)
cat-iso-hset x y = iso-h
  ( record
    { to = λ { ((t , f) , (i₁ , i₂)) → c-iso t f i₁ i₂ }
    ; from = λ { (c-iso t f i₁ i₂) → ((t , f) , (i₁ , i₂)) }
    ; iso₁ = λ _ → refl
    ; iso₂ = λ _ → refl } )
  ( Σ-hlevel ( ×-hlevel (trunc x y) (trunc y x)) (λ { (t , f)
             → h↑ (×-hlevel (trunc x x (f ∘ t) (id x))
                            (trunc y y (t ∘ f) (id y))) }) )
