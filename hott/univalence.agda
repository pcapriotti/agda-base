{-# OPTIONS --without-K #-}
module hott.univalence where

open import level using (lsuc)
open import sum using (_,_ ; proj₁)
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core using (_$_ ; id ; _∘_)
open import function.isomorphism using (_≅_ ; module _≅_)
open import hott.weak-equivalence.core

-- mapping from equality to function
coerce : ∀ {i} {X Y : Set i} → X ≡ Y → X → Y
coerce refl = id

coerce-equiv : ∀ {i} {X Y : Set i} → (p : X ≡ Y) → weak-equiv (coerce p)
coerce-equiv refl x = (x , refl) , λ { (.x , refl) → refl }

coerce-hom : ∀ {i} {X Y Z : Set i}
           → (p : X ≡ Y)(q : Y ≡ Z)
           → coerce (p ⊚ q) ≡ coerce q ∘ coerce p
coerce-hom refl q = refl

-- mapping from propositional equality to weak equivalence
≡⇒≈ : ∀ {i} {X Y : Set i} → X ≡ Y → X ≈ Y
≡⇒≈ p = coerce p , coerce-equiv p

Univalence : ∀ i → Set (lsuc i)
Univalence i = {X Y : Set i} → weak-equiv $ ≡⇒≈ {X = X} {Y = Y}

postulate univalence : ∀ {i} → Univalence i

private
  module Properties {i} {X Y : Set i} where
    uni-equiv : (X ≡ Y) ≈ (X ≈ Y)
    uni-equiv = ≡⇒≈ , univalence

    uni-iso : (X ≡ Y) ≅ (X ≈ Y)
    uni-iso = ≈⇒≅ uni-equiv
    open _≅_ uni-iso public using ()
      renaming (from to ≈⇒≡)

    uni-coherence : (f : X ≈ Y) → coerce (≈⇒≡ f) ≡ proj₁ f
    uni-coherence f = begin
        coerce (≈⇒≡ f)
      ≡⟨ refl ⟩
        proj₁ (≡⇒≈ (≈⇒≡ f))
      ≡⟨ cong proj₁ (iso₂ f) ⟩
        proj₁ f
      ∎
      where
        open ≡-Reasoning
        open _≅_ uni-iso using (iso₂)

open Properties public
