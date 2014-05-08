{-# OPTIONS --without-K --type-in-type #-}
module hott.univalence where

open import sum using (_,_ ; proj₁)
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.isomorphism.core using (_≅_ ; module _≅_)
open import hott.weak-equivalence.core

-- mapping from equality to function
coerce : {X Y : Set} → X ≡ Y → X → Y
coerce refl = id

coerce-equiv : {X Y : Set} → (p : X ≡ Y) → weak-equiv (coerce p)
coerce-equiv refl x = (x , refl) , λ { (.x , refl) → refl }

coerce-hom : {X Y Z : Set}
           → (p : X ≡ Y)(q : Y ≡ Z)
           → coerce (p · q) ≡ coerce q ∘ coerce p
coerce-hom refl q = refl

-- mapping from propositional equality to weak equivalence
≡⇒≈ : {X Y : Set} → X ≡ Y → X ≈ Y
≡⇒≈ p = coerce p , coerce-equiv p

Univalence : Set
Univalence = {X Y : Set} → weak-equiv $ ≡⇒≈ {X = X} {Y = Y}

postulate univalence : Univalence

private
  module Properties {X Y : Set} where
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
      ≡⟨ ap proj₁ (iso₂ f) ⟩
        proj₁ f
      ∎
      where
        open ≡-Reasoning
        open _≅_ uni-iso using (iso₂)

open Properties public
