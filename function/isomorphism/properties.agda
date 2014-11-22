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
open import function.isomorphism.utils
open import hott.equivalence.core
open import hott.equivalence.alternative
open import hott.level.core
open import sets.unit

-- lifting is an isomorphism
lift-iso : ∀ {i} j (X : Set i) → X ≅ ↑ j X
lift-iso j X = iso lift lower (λ _ → refl) (λ _ → refl)

iso-adjunction : ∀ {i j}{X : Set i}{Y : Set j}
               → (isom : X ≅ Y)(x : X)(y : Y)
               → (apply isom x ≡ y) ≅ (x ≡ invert isom y)
iso-adjunction {i}{j}{X}{Y} isom x y
  = lift-iso i (to x ≡ y)
  ·≅ ≡⇒≅ (funext-inv eq' (y , x))
  ·≅ sym≅ (lift-iso j (x ≡ from y))
  where
    open _≅_ isom
    open ≅-Reasoning

    to-we : weak-equiv to
    to-we = proj₂ (≅⇒≈ isom)

    P₁ : Y × X → Set (i ⊔ j)
    P₁ (y , x) = ↑ i (to x ≡ y)

    p₁ : Σ (Y × X) P₁ → Y × X
    p₁ = proj₁

    P₂ : Y × X → Set (i ⊔ j)
    P₂ (y , x) = ↑ j (x ≡ from y)

    p₂ : Σ (Y × X) P₂ → Y × X
    p₂ = proj₁

    total : Σ (Y × X) P₁ ≅ Σ (Y × X) P₂
    total = Σ-assoc-iso
          ·≅ ( Σ-ap-iso refl≅ λ y
             → (Σ-ap-iso refl≅ λ x → sym≅ (lift-iso _ _))
             ·≅ contr-⊤-iso (to-we y)
             ·≅ sym≅ (contr-⊤-iso (singl-contr' (from y)))
             ·≅ (Σ-ap-iso refl≅ λ x → lift-iso _ _) )
          ·≅ sym≅ Σ-assoc-iso

    comm : (a : Σ (Y × X) P₁) → p₁ a ≡ p₂ (apply total a)
    comm ((y , x) , lift q) = ap (_,_ y) (sym (iso₁ x) · ap from q)

    eq' : P₁ ≡ P₂
    eq' = iso⇒inj (sym≅ (fibration-iso j))
          (invert (fib-eq-iso p₁ p₂) (≅⇒≅' total , funext comm))

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
