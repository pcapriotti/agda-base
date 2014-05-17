{-# OPTIONS --without-K #-}

module hott.truncation.const where

open import sum
open import equality
open import hott.truncation.core
open import hott.hlevel

const-factorisation : ∀ {i j}{A : Set i}{B : Set j}
                    → h 2 B
                    → (f : A → B)
                    → ((x y : A) → f x ≡ f y)
                    → (∥ A ∥ → B)
const-factorisation {A = A}{B} hB f c = f'
  where
    E : Set _
    E = Σ B λ b → (a : A) → f a ≡ b

    p : E → B
    p (b , _) = b

    lem : (a₀ : A)(b : B)(u : (a : A) → f a ≡ b)
        → (_≡_ {A = E} (f a₀ , λ a → c a a₀) (b , u))
    lem a₀ b u = unapΣ (u a₀ , h1⇒prop (Π-hlevel (λ a → hB (f a) b)) _ u)

    hE : A → contr E
    hE a₀ = (f a₀ , λ a → c a a₀) , λ { (b , u) → lem a₀ b u }

    u : ∥ A ∥ → contr E
    u = elim' (contr-h1 E) hE

    s : ∥ A ∥ → E
    s a = proj₁ (u a)

    f' : ∥ A ∥ → B
    f' a = p (s a)
