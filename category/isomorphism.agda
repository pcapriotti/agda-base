{-# OPTIONS --without-K #-}
open import category.category

module category.isomorphism where

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
  field
    to : hom x y
    from : hom y x

    iso₁ : from ∘ to ≡ id x
    iso₂ : to ∘ from ≡ id y

≡⇒iso : ∀ {i j}(C : Category i j){x y : obj C} → x ≡ y → cat-iso C x y
≡⇒iso C {x}{.x} refl = record
  { to = id x
  ; from = id x
  ; iso₁ = left-unit _
  ; iso₂ = left-unit _ }

private
  module Properties {i j}{C : Category i j}(x y : obj C) where
    inverses : hom x y × hom y x → Set _
    inverses (t , f) = f ∘ t ≡ id x
                     × t ∘ f ≡ id y

    inverses-h1 : ∀ tf → h 1 (inverses tf)
    inverses-h1 (t , f) =
      ×-hlevel (trunc C x x (f ∘ t) (id x))
               (trunc C y y (t ∘ f) (id y))

    E : Set _
    E = Σ (hom x y × hom y x) inverses

    e-iso : E ≅ cat-iso C x y
    e-iso = record
      { to = λ { ((t , f) , (i₁ , i₂)) → c-iso t f i₁ i₂ }
      ; from = λ { (c-iso t f i₁ i₂) → ((t , f) , (i₁ , i₂)) }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }

cat-iso-hset : ∀ {i j}{C : Category i j} (x y : obj C) → h 2 (cat-iso C x y)
cat-iso-hset {C = C} x y = iso-hlevel e-iso
  ( Σ-hlevel (×-hlevel (trunc C x y) (trunc C y x))
             (λ tf → h↑ (inverses-h1 tf)) )
  where
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
