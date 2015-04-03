{-# OPTIONS --without-K #-}
module function.isomorphism.properties where

open import level
open import sum
open import sets.nat.core
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.fibration
open import function.overloading
open import function.extensionality.core
open import function.extensionality.proof
open import function.isomorphism.core
open import function.isomorphism.coherent
open import function.isomorphism.lift
open import function.isomorphism.utils
open import function.isomorphism.two-out-of-six
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

private
  iso≡-lem : ∀ {i j}{X : Set i}{Y : Set j}
           → (isom : X ≅ Y)
           → (x x' : X)
           → weak-equiv (λ (p : x ≡ x') → ap (invert isom) (ap (apply isom) p))
  iso≡-lem {X = X} isom x x' = step₃
    where
      step₁ : ∀ {k}{A : Set k}(a a' : A)
            → weak-equiv {X = a ≡ a'} {Y = a ≡ a'} (ap (λ x → x))
      step₁ a a' = subst weak-equiv (sym (funext ap-id)) (proj₂ (≅⇒≈ refl≅))

      step₂ : weak-equiv (λ (p : x ≡ x') → ap (invert isom ∘ apply isom) p)
      step₂ = subst (λ u → weak-equiv {X = x ≡ x'} (ap u)) (sym (funext (_≅_.iso₁ isom)))
                    (step₁ x x')

      step₃ = subst weak-equiv (sym (funext λ p → ap-hom (apply isom) (invert isom) p)) step₂

iso≡ : ∀ {i j}{X : Set i}{Y : Set j}
     → (isom : X ≅ Y)
     → {x x' : X}
     → (x ≡ x')
     ≅ (apply isom x ≡ apply isom x')
iso≡ isom {x}{x'} = two-out-of-six.f-iso
  (ap (apply isom))
  (ap (invert isom))
  (ap (apply isom))
  (iso≡-lem isom x x')
  (iso≡-lem (sym≅ isom) (apply isom x) (apply isom x'))

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
