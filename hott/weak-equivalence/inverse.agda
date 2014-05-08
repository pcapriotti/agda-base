{-# OPTIONS --without-K --type-in-type #-}
module hott.weak-equivalence.inverse where

open import sum
open import function.core
open import function.isomorphism.core
open import function.isomorphism.utils
open import function.isomorphism.properties
open import function.extensionality
open import equality.core
open import sets.unit
open import sets.nat using (suc)
open import hott.hlevel
open import hott.weak-equivalence.core
open import hott.weak-equivalence.alternative
open import hott.univalence

module _ {A : Set}{B : Set} where
  record inverse (f : A → B) : Set where
    constructor mk-inverse
    field
      g : B → A
      α : (x : A) → g (f x) ≡ x
      β : (y : B) → f (g y) ≡ y

    isom : A ≅ B
    isom = iso f g α β

  iso⇒inv : (f : A ≅ B) → inverse (apply≅ f)
  iso⇒inv (iso f g α β) = mk-inverse g α β

  inverse-struct-iso : (f : A → B)
                     → inverse f
                     ≅ ( Σ (B → A) λ g
                       → Σ ((x : A) → g (f x) ≡ x) λ α
                       → ((y : B) → f (g y) ≡ y) )
  inverse-struct-iso f = record
    { to = λ { (mk-inverse g α β) → (g , α , β) }
    ; from = λ { (g , α , β) → (mk-inverse g α β) }
    ; iso₁ = λ _ → refl
    ; iso₂ = λ _ → refl }

  ≅-inv-struct-iso : (A ≅ B) ≅ Σ (A → B) inverse
  ≅-inv-struct-iso = trans≅ ≅-struct-iso
    (Σ-ap-iso₂ (λ f → sym≅ (inverse-struct-iso f)))

ind-≈ : (P : ∀ {A B : Set} → A ≈ B → Set)
      → (∀ {A : Set} → P {A = A} (≡⇒≈ refl))
      → ∀ {A B : Set}(eq : A ≈ B) → P eq
ind-≈ P d {A = A} eq = subst P (_≅_.iso₂ uni-iso eq)
                               (lem (≈⇒≡ eq))
  where
    lem : ∀ {A B : Set}
        → (p : A ≡ B)
        → P (≡⇒≈ p)
    lem refl = d

inverse-nonprop' : {A : Set}
                 → inverse (λ (x : A) → x)
                 ≅ ((x : A) → x ≡ x)
inverse-nonprop' {A} = begin
    inverse id'
  ≅⟨ inverse-struct-iso id' ⟩
    ( Σ (A → A) λ g
    → Σ ((x : A) → g x ≡ x) λ α
    → ((y : A) → g y  ≡ y) )
  ≅⟨ ( Σ-ap-iso₂ λ g
      → Σ-ap-iso₁ strong-funext-iso ) ⟩
    ( Σ (A → A) λ g
    → Σ (g ≡ id') λ α
    → ((y : A) → g y ≡ y) )
  ≅⟨ sym≅ Σ-assoc-iso ⟩
    ( Σ (singleton' id') λ { (g , α)
    → ((y : A) → g y ≡ y) } )
  ≅⟨ trans≅ (Σ-ap-iso' (contr-⊤-iso (singl-contr' id'))
                       (λ _ → refl≅))
            ×-left-unit ⟩
    ((x : A) → x ≡ x)
  ∎
  where
    open ≅-Reasoning
    id' : A → A
    id' x = x

inverse-nonprop : {A B : Set}
                → (f : A → B)
                → weak-equiv f
                → inverse f
                ≅ ((x : A) → x ≡ x)
inverse-nonprop {A} f we = ind-≈ P inverse-nonprop' (f , we)
  where
    P : {A B : Set} → A ≈ B → Set
    P {A = A} (f , we) = inverse f ≅ ((x : A) → x ≡ x)

