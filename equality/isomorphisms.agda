{-# OPTIONS --without-K #-}
module equality.isomorphisms where

open import sum
open import equality.core
open import equality.calculus
open import function
open import function.isomorphism
open import hott.coherence

Σ-split-iso : ∀ {i j}{X : Set i}{Y : X → Set j}
            → {a a' : X}{b : Y a}{b' : Y a'}
            → (Σ (a ≡ a') λ q → subst Y q b ≡ b')
            ≅ ((a , b) ≡ (a' , b'))
Σ-split-iso {Y = Y}{a}{a'}{b}{b'} = iso uncongΣ congΣ H K
  where
    H : ∀ {a a'}{b : Y a}{b' : Y a'}
      → (p : Σ (a ≡ a') λ q → subst Y q b ≡ b')
      → congΣ (uncongΣ {a = a}{a' = a'}{b = b}{b' = b'} p) ≡ p
    H (refl , refl) = refl

    K : (p : (a , b) ≡ (a' , b')) → uncongΣ (congΣ p) ≡ p
    K = J (λ u v p → uncongΣ (congΣ p) ≡ p)
          (λ {(a , b) → refl })
          (a , b) (a' , b')

Σ-split : ∀ {i j}{X : Set i}{Y : X → Set j}
        → {a a' : X}{b : Y a}{b' : Y a'}
        → (Σ (a ≡ a') λ q → subst Y q b ≡ b')
        ≡ ((a , b) ≡ (a' , b'))
Σ-split = ≅⇒≡ Σ-split-iso

ΠΣ-swap-iso : ∀ {i j k}{X : Set i}{Y : X → Set j}
            → {Z : (x : X) → Y x → Set k}
            → ((x : X) → Σ (Y x) λ y → Z x y)
            ≅ (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap-iso = record
  { to = λ f → (proj₁ ∘ f , proj₂ ∘ f)
  ; from = λ { (f , g) x → (f x , g x) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

ΠΣ-swap : ∀ {i j k}{X : Set i}{Y : X → Set j}
        → {Z : (x : X) → Y x → Set k}
        → ((x : X) → Σ (Y x) λ y → Z x y)
        ≡ (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap = ≅⇒≡ ΠΣ-swap-iso

-- rewriting lemmas for equations on equalities
sym≡ : ∀ {i}{X : Set i}{x y : X}
      → (p q : x ≡ y)
      → (p ≡ q)
      ≡ (q ≡ p)
sym≡ p q = ≅⇒≡ (iso sym sym double-inverse double-inverse)

move-≡ : ∀ {i}{X : Set i}{x y z : X}
       → (p : x ≡ y)(q : y ≡ z)(r : x ≡ z)
       → (p ⊚ q ≡ r)
       ≡ (sym p ⊚ r ≡ q)
move-≡ refl = sym≡
