{-# OPTIONS --type-in-type --without-K #-}

module category.isomorphism where

open import category.category
open import category.graph
open import hott.hlevel.properties
open import function.core
open import function.isomorphism
open import function.overloading
open import sum
open import equality.core
open import equality.calculus using (uncongΣ)
open import hott.hlevel

record cat-iso (C : Category)(x y : obj C) : Set where
  constructor c-iso
  open as-category C
  field
    to : hom x y
    from : hom y x

    iso₁ : from ∘ to ≡ id
    iso₂ : to ∘ from ≡ id

≡⇒iso : (C : Category){x y : obj C} → x ≡ y → cat-iso C x y
≡⇒iso C {x}{.x} refl = record
  { to = id
  ; from = id
  ; iso₁ = left-id _
  ; iso₂ = left-id _ }
  where open as-category C

private
  module properties {C : Category}(x y : obj C) where
    open as-category C
    inverses : hom x y × hom y x → Set
    inverses (t , f) = f ∘ t ≡ id
                     × t ∘ f ≡ id

    inverses-h1 : ∀ tf → h 1 (inverses tf)
    inverses-h1 (t , f) =
      ×-hlevel (trunc x x (f ∘ t) id)
               (trunc y y (t ∘ f) id)

    E : Set
    E = Σ (hom x y × hom y x) inverses

    e-iso : E ≅ cat-iso C x y
    e-iso = record
      { to = λ { ((t , f) , (i₁ , i₂)) → c-iso t f i₁ i₂ }
      ; from = λ { (c-iso t f i₁ i₂) → ((t , f) , (i₁ , i₂)) }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }

cat-iso-hset : {C : Category} (x y : obj C) → h 2 (cat-iso C x y)
cat-iso-hset {C = C} x y = iso-hlevel e-iso
  ( Σ-hlevel (×-hlevel (trunc x y) (trunc y x))
             (λ tf → h↑ (inverses-h1 tf)) )
  where
    open as-category C
    open properties x y

cat-iso-equality : {C : Category}{x y : obj C}
                   {p q : cat-iso C x y}
                 → (cat-iso.to p ≡ cat-iso.to q)
                 → (cat-iso.from p ≡ cat-iso.from q)
                 → p ≡ q
cat-iso-equality {C = C}{x}{y}{p}{q} t f = cong (apply e-iso)
  (uncongΣ (cong₂ _,_ t f , h1⇒prop (inverses-h1 _) _ _))
  where open properties x y

open properties public
