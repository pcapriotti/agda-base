{-# OPTIONS --without-K #-}
module function.isomorphism.properties where

open import level
open import sum
open import sets.nat.core
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.fibration
open import function.overloading
open import function.extensionality.core
open import function.extensionality.proof
open import function.isomorphism.core
open import function.isomorphism.coherent
open import function.isomorphism.lift
open import function.isomorphism.utils
open import hott.equivalence.core
open import hott.equivalence.alternative
open import hott.level.core
open import sets.unit

iso-adjunction : ∀ {i j}{X : Set i}{Y : Set j}
               → (isom : X ≅ Y)(x : X)(y : Y)
               → (apply isom x ≡ y) ≅ (x ≡ invert isom y)
iso-adjunction {i}{j}{X}{Y} isom x y
  = family-eq-iso total' (λ { (y , x) q → comm' x y q }) (y , x)
  where
    open _≅_ isom
    open ≅-Reasoning

    to-we : weak-equiv to
    to-we = proj₂ (≅⇒≈ isom)

    total' : (Σ (Y × X) λ { (y , x) → to x ≡ y })
           ≅ (Σ (Y × X) λ { (y , x) → x ≡ from y})
    total' = Σ-assoc-iso
           ·≅ ( Σ-ap-iso refl≅ λ y
              → contr-⊤-iso (to-we y)
              ·≅ sym≅ (contr-⊤-iso (singl-contr' (from y))) )
           ·≅ sym≅ Σ-assoc-iso

    comm' : (x : X)(y : Y)(p : to x ≡ y)
          → proj₁ (apply total' ((y , x) , p)) ≡ (y , x)
    comm' x y q = ap (_,_ y) (sym (ap from q) · iso₁ x)

iso≡ : ∀ {i j}{X : Set i}{Y : Set j}
     → (isom : X ≅ Y)
     → {x x' : X}
     → (x ≡ x')
     ≅ (apply isom x ≡ apply isom x')
iso≡ isom {x}{x'} = trans≡-iso (_≅_.iso₁ isom x)
                  ·≅ iso-adjunction (sym≅ isom) _ _

abstract
  subtype-eq : ∀ {i j k}{A : Set i}{P : A → Set j}
             → ((x : A) → h 1 (P x))
             → {X : Set k}
             → (isom : X ≅ Σ A P)
             → {x y : X}
             → (proj₁ (apply isom x) ≡ proj₁ (apply isom y))
             → x ≡ y
  subtype-eq hP isom p = iso⇒inj isom
    (unapΣ (p , h1⇒prop (hP _) _ _))
