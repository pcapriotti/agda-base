{-# OPTIONS --without-K #-}
module equality.isomorphisms where

open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function
open import function.isomorphism
open import hott.coherence
open import hott.univalence

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

Σ-cong : ∀ {i j}{X : Set i}{X' : Set i}{Y : X → Set j}
       → (p : X ≡ X')
       → (Σ X Y ≡ Σ X' (Y ∘ invert (refl≅ p)))
Σ-cong {X = X}{.X}{Y} refl = refl

Σ-cong-iso : ∀ {i i' j}{X : Set i}{X' : Set i'}{Y : X → Set j}
           → (isom : X ≅' X')
           → Σ X Y ≅ Σ X' (Y ∘ _≅_.from (proj₁ isom))
Σ-cong-iso {X = X}{X'}{Y} (iso f g H K , γ) = record
  { to = λ { (x , y) → (f x , subst Y (sym (H x)) y) }
  ; from = λ { (x , y) → (g x , y) }
  ; iso₁ = λ { (x , y) → uncongΣ (H x ,
        subst-hom Y (sym (H x)) (H x) y
      ⊚ cong (λ p → subst Y p y) (right-inverse (H x)) ) }
  ; iso₂ = λ { (x , y) → uncongΣ (K x ,
        subst-naturality Y g (K x) _
      ⊚ (subst-hom Y (sym (H (g x))) (cong g (K x)) y
      ⊚ cong (λ p → subst Y p y) (lem x) ) ) } }
  where
    open ≡-Reasoning
    lem : (x : X') → sym (H (g x)) ⊚ cong g (K x) ≡ refl
    lem x = cong (λ z → sym (H (g x)) ⊚ z) (coCoherence _ γ x)
          ⊚ right-inverse (H (g x))

ΠΣ-swap-iso : ∀ {i j k}{X : Set i}{Y : X → Set j}
            → {Z : (x : X) → Y x → Set k}
            → ((x : X) → Σ (Y x) λ y → Z x y)
            ≅' (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap-iso = record
  { to = λ f → (proj₁ ∘ f , proj₂ ∘ f)
  ; from = λ { (f , g) x → (f x , g x) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }
  , λ _ → refl

ΠΣ-swap : ∀ {i j k}{X : Set i}{Y : X → Set j}
        → {Z : (x : X) → Y x → Set k}
        → ((x : X) → Σ (Y x) λ y → Z x y)
        ≡ (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap = ≈⇒≡ (≅'⇒≈ ΠΣ-swap-iso)

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
