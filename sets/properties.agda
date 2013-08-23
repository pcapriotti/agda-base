{-# OPTIONS --without-K #-}
module sets.properties where

open import sum
open import equality.core
open import equality.calculus
open import function.isomorphism
open import function.overloading
open import hott.hlevel
open import hott.weak-equivalence
open import sets.unit

mk-prop-iso : ∀ {i j}{A : Set i}{B : Set j}
            → h 1 A → h 1 B
            → (A → B) → (B → A)
            → A ≅ B
mk-prop-iso hA hB f g
  = iso f g (λ x → h1⇒prop hA _ _)
            (λ y → h1⇒prop hB _ _)

iso-coherence-h2 : ∀ {i j}(A : HSet i)(B : HSet j)
                 → (proj₁ A ≅' proj₁ B)
                 ≅ (proj₁ A ≅ proj₁ B)
iso-coherence-h2 (A , hA)(B , hB) = begin
    (A ≅' B)
  ≅⟨ ( Σ-ap-iso₂ λ isom
      → contr-⊤-iso (Π-hlevel λ x → hB _ _ _ _) ) ⟩
    ((A ≅ B) × ⊤)
  ≅⟨ ×-right-unit ⟩
    (A ≅ B)
  ∎
  where open ≅-Reasoning

iso-equiv-h2 : ∀ {i j}{A : Set i}{B : Set j}
             → h 2 A → h 2 B
             → (A ≈ B) ≅ (A ≅ B)
iso-equiv-h2 hA hB = trans≅ ≈⇔≅'
  (iso-coherence-h2 (_ , hA) (_ , hB))

iso-eq-h2 : ∀ {i j}{A : Set i}{B : Set j}
          → h 2 A → h 2 B
          → {isom isom' : A ≅ B}
          → (apply isom ≡ apply isom')
          → isom ≡ isom'
iso-eq-h2 hA hB p =
  subtype-eq (λ f → weak-equiv-h1 f)
             (sym≅ (iso-equiv-h2 hA hB)) p

inj-eq-h2 : ∀ {i j}{A : Set i}{B : Set j}
          → h 2 A → {f f' : A ↣ B}
          → (apply f ≡ apply f')
          → f ≡ f'
inj-eq-h2 hA refl
  = ap (_,_ _) (h1⇒prop (inj-hlevel _ hA) _ _)
