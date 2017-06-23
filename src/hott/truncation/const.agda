{-# OPTIONS --without-K #-}

module hott.truncation.const where

open import sum
open import equality
open import function.overloading
open import hott.truncation.core
open import hott.level

const-factorisation : ∀ {i j}{A : Set i}{B : Set j}
                    → h 2 B
                    → (f : A → B)
                    → ((x y : A) → f x ≡ f y)
                    → (Trunc 1 A → B)
const-factorisation {A = A}{B} hB f c = f'
  where
    E : Set _
    E = Σ B λ b → (a : A) → f a ≡ b

    p : E → B
    p (b , _) = b

    lem : (a₀ : A)(b : B)(u : (a : A) → f a ≡ b)
        → (_≡_ {A = E} (f a₀ , λ a → c a a₀) (b , u))
    lem a₀ b u = unapΣ (u a₀ , h1⇒prop (Π-level (λ a → hB (f a) b)) _ u)

    hE : A → contr E
    hE a₀ = (f a₀ , λ a → c a a₀) , λ { (b , u) → lem a₀ b u }

    u : Trunc 1 A → contr E
    u = Trunc-elim 1 _ _ (contr-h1 E) hE

    s : Trunc 1 A → E
    s a = proj₁ (u a)

    f' : Trunc 1 A → B
    f' a = p (s a)
