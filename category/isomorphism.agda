{-# OPTIONS --without-K #-}
open import category.category

module category.isomorphism {i j}(C : Category i j) where

open import hott.hlevel.properties
open import hott.univalence.properties
open import function.isomorphism
  renaming (apply to apply≅)
open import function.isomorphism.properties
open import sum
open import equality.core
open import equality.calculus using (uncongΣ)
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

private
  module Properties (x y : obj) where
    inverses : hom x y × hom y x → Set _
    inverses (t , f) = f ∘ t ≡ id x
                     × t ∘ f ≡ id y

    inverses-h1 : ∀ tf → h 1 (inverses tf)
    inverses-h1 (t , f) =
      ×-hlevel (trunc x x (f ∘ t) (id x))
               (trunc y y (t ∘ f) (id y))

    E : Set _
    E = Σ (hom x y × hom y x) inverses

    e-iso : E ≅ cat-iso x y
    e-iso = record
      { to = λ { ((t , f) , (i₁ , i₂)) → c-iso t f i₁ i₂ }
      ; from = λ { (c-iso t f i₁ i₂) → ((t , f) , (i₁ , i₂)) }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }

    cat-iso-hset : h 2 (cat-iso x y)
    cat-iso-hset = iso-h e-iso
      ( Σ-hlevel (×-hlevel (trunc x y) (trunc y x))
                 (λ tf → h↑ (inverses-h1 tf)) )

    cat-iso-equality : {p q : cat-iso x y}
                     → (cat-iso.to p ≡ cat-iso.to q)
                     → (cat-iso.from p ≡ cat-iso.from q)
                     → p ≡ q
    cat-iso-equality {p}{q} t f = cong (apply≅ e-iso)
      (uncongΣ (cong₂ _,_ t f , h1⇒prop (inverses-h1 _) _ _))

open Properties public
