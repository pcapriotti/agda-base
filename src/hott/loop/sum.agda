{-# OPTIONS --without-K #-}
module hott.loop.sum where

open import sum
open import equality
open import function.core
open import function.extensionality
open import function.isomorphism
open import function.overloading
open import sets.nat
open import pointed
open import hott.equivalence
open import hott.level.core
open import hott.loop.core
open import hott.loop.properties

private
  abstract
    loop-sum' : ∀ {i}{j}{A : Set i}{B : A → Set j}(n : ℕ)
              → (hB : (a : A) → h n (B a))
              → {a₀ : A}{b₀ : B a₀}
              → Ω n {Σ A B} (a₀ , b₀) ≅ Ω n a₀
    loop-sum' 0 hB {a₀}{b₀} = Σ-ap-iso refl≅ (λ a → contr-⊤-iso (hB a)) ·≅ ×-right-unit
    loop-sum' {A = A}{B = B} (suc n) hB {a₀}{b₀} = Ω-iso n (sym≅ Σ-split-iso) refl
                                                ·≅ loop-sum' n λ p → hB _ _ _

    loop-sum-β : ∀ {i}{j}{A : Set i}{B : A → Set j}(n : ℕ)
               → (hB : (a : A) → h n (B a))
               → {a₀ : A}{b₀ : B a₀}
               → (p : Ω n {Σ A B} (a₀ , b₀))
               → apply≅ (loop-sum' n hB) p ≡ mapΩ n proj₁ p
    loop-sum-β zero hB p = refl
    loop-sum-β (suc n) hB p
      = loop-sum-β n _ (mapΩ n apΣ p)
      · mapΩ-hom n apΣ proj₁ p
      · funext-inv (ap proj₁ (ap (mapΩP n) lem)) p
      where
        lem : ∀ {i}{j}{A : Set i}{B : A → Set j}{a₀ : A}{b₀ : B a₀}
            → _≡_ {A = PMap (_≡_ {A = Σ A B} (a₀ , b₀) (a₀ , b₀) , refl) ((a₀ ≡ a₀) , refl)}
              (proj₁ ∘ apΣ , refl)
              (ap proj₁ , refl)
        lem = apply≅ pmap-eq ((λ _ → refl) , refl)


loop-sum : ∀ {i}{j}{A : Set i}{B : A → Set j}(n : ℕ)
         → (hB : (a : A) → h n (B a))
         → {a₀ : A}{b₀ : B a₀}
         → Ω n {Σ A B} (a₀ , b₀) ≅ Ω n a₀
loop-sum n hB {a₀}{b₀} = ≈⇒≅ (mapΩ n proj₁ , subst weak-equiv eq we)
  where
    abstract
      we : weak-equiv (apply (loop-sum' n hB {a₀}{b₀}))
      we = proj₂ (≅⇒≈ (loop-sum' n hB))

      eq : apply (loop-sum' n hB {a₀}{b₀}) ≡ mapΩ n proj₁
      eq = funext (loop-sum-β n hB)
