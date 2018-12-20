module algebra.group.classifying where

open import level
open import algebra.group.core
open import algebra.group.morphism
open import equality.core
open import function.isomorphism
open import pointed.core
open import sets.unit
open import sum
open import hott.level.core
open import hott.loop.core
open import hott.truncation.core
open import hott.equivalence

module _ {i}(G : Set i) ⦃ gG : IsGroup G ⦄ where
  open import algebra.group.gset G
  open IsGroup ⦃ ... ⦄

  -- G as a G-Set
  G' : GSet i
  G' = (G , GisGSet)

  -- G as a pointed set
  G* : PSet i
  G* = (G , e)

  𝑩 : Set (lsuc i)
  𝑩 = Σ (GSet i) λ X → Trunc 1 (X ≡ G')

  base : 𝑩
  base = (G' , [ refl ])

  𝑩* : PSet (lsuc i)
  𝑩* = (𝑩 , base)

  𝑩-Ω : (base ≡ base) ≅ G
  𝑩-Ω = begin
      (base ≡ base)
    ≅⟨ sym≅ Σ-split-iso ⟩
      ( Σ (G' ≡ G') λ p
      → subst (λ X → Trunc 1 (X ≡ G')) p [ refl ] ≡ [ refl ] )
    ≅⟨ (Σ-ap-iso refl≅ λ p → contr-⊤-iso (Trunc-level 1 _ _)) ·≅ ×-right-unit ⟩
      (G' ≡ G')
    ≅⟨ GSet-univalence G G ⟩
      ( Σ (GSetMorphism G G) λ { (f , _) → weak-equiv f } )
    ≅⟨ ( Σ-ap-iso' (GSet-repr-iso is-set) λ _ → refl≅ ) ⟩
      ( Σ G λ { g → weak-equiv (λ x → x * g) } )
    ≅⟨ ( Σ-ap-iso refl≅ λ g → contr-⊤-iso ( lem g , h1⇒prop (we-h1 _) _ ) )
        ·≅ ×-right-unit ⟩
      G
    ∎
    where
      open ≅-Reasoning
      lem : (g : G) → weak-equiv (λ x → x * g)
      lem g = proj₂ (≅'⇒≈ (≅⇒≅' (right-translation-iso g)))
