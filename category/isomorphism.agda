{-# OPTIONS --without-K #-}
open import category.category

module category.isomorphism where

open import category.structure
open import category.graph
open import hott.hlevel.properties
open import function.isomorphism
  renaming (apply to apply≅)
open import function.isomorphism.properties
open import sum
open import equality.core
open import equality.calculus using (uncongΣ)
open import hott.hlevel

record cat-iso {i j}(C : Category i j)(x y : obj C) : Set j where
  constructor c-iso
  open cat-interface C
  field
    to : hom C x y
    from : hom C y x

    iso₁ : from ∘ to ≡ id
    iso₂ : to ∘ from ≡ id

≡⇒iso : ∀ {i j}(C : Category i j){x y : obj C} → x ≡ y → cat-iso C x y
≡⇒iso C {x}{.x} refl = record
  { to = id
  ; from = id
  ; iso₁ = left-unit _
  ; iso₂ = left-unit _ }
  where open cat-interface C

private
  module Properties {i j}{C : Category i j}(x y : obj C) where
    open cat-interface C
    inverses : hom C x y × hom C y x → Set _
    inverses (t , f) = f ∘ t ≡ id
                     × t ∘ f ≡ id

    inverses-h1 : ∀ tf → h 1 (inverses tf)
    inverses-h1 (t , f) =
      ×-hlevel (trunc x x (f ∘ t) id)
               (trunc y y (t ∘ f) id)

    E : Set _
    E = Σ (hom C x y × hom C y x) inverses

    e-iso : E ≅ cat-iso C x y
    e-iso = record
      { to = λ { ((t , f) , (i₁ , i₂)) → c-iso t f i₁ i₂ }
      ; from = λ { (c-iso t f i₁ i₂) → ((t , f) , (i₁ , i₂)) }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }

cat-iso-hset : ∀ {i j}{C : Category i j} (x y : obj C) → h 2 (cat-iso C x y)
cat-iso-hset {C = C} x y = iso-hlevel e-iso
  ( Σ-hlevel (×-hlevel (trunc x y) (trunc y x))
             (λ tf → h↑ (inverses-h1 tf)) )
  where
    open cat-interface C
    open Properties x y

cat-iso-equality : ∀ {i j}{C : Category i j}{x y : obj C}
                   {p q : cat-iso C x y}
                 → (cat-iso.to p ≡ cat-iso.to q)
                 → (cat-iso.from p ≡ cat-iso.from q)
                 → p ≡ q
cat-iso-equality {C = C}{x}{y}{p}{q} t f = cong (apply≅ e-iso)
  (uncongΣ (cong₂ _,_ t f , h1⇒prop (inverses-h1 _) _ _))
  where open Properties x y

open Properties public
