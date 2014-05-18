{-# OPTIONS --without-K #-}

module function.surjective where

open import sum
open import equality
open import function.isomorphism.core
open import hott.level.core
open import hott.equivalence.core
open import hott.truncation

surjective : ∀ {i j}{A : Set i}{B : Set j} → (A → B) → Set _
surjective f = ∀ b → ∥ f ⁻¹ b ∥

retr⇒surj : ∀ {i j}{A : Set i}{B : Set j}
          → (f : A → B)
          → retraction f
          → surjective f
retr⇒surj f retr b = η (retr b)

inj+surj⇒eq : ∀ {i j}{A : Set i}{B : Set j}
            → h 2 A → h 2 B
            → (f : A → B)
            → injective f
            → surjective f
            → weak-equiv f
inj+surj⇒eq {A = A}{B = B} hA hB f inj surj b = retr-f b , propFib b (retr-f b)
  where
    propFib : (b : B) → prop (f ⁻¹ b)
    propFib b (a , p) (a' , p') = unapΣ (inj (p · sym p') , h1⇒prop (hB (f a') b) _ _)

    retr-f : retraction f
    retr-f b = Trunc-elim (prop⇒h1 (propFib b)) (λ x → x) (surj b)
