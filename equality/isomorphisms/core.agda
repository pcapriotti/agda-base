{-# OPTIONS --without-K #-}
module equality.isomorphisms.core where

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

Σ-cong-iso : ∀ {i i' j}{X : Set i}{X' : Set i'}{Y : X → Set j}
           → (isom : X ≅ X')
           → Σ X Y ≅ Σ X' (Y ∘ _≅_.from isom)
Σ-cong-iso {X = X}{X'}{Y} isom = record
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
    isom' = ≅⇒≅' isom
    γ = proj₂ isom'
    open _≅_ (proj₁ isom')
      renaming ( to to f ; from to g
               ; iso₁ to H; iso₂ to K )

    lem : (x : X') → sym (H (g x)) ⊚ cong g (K x) ≡ refl
    lem x = cong (λ z → sym (H (g x)) ⊚ z) (coCoherence _ γ x)
          ⊚ right-inverse (H (g x))

ΠΣ-swap-iso : ∀ {i j k}{X : Set i}{Y : X → Set j}
            → {Z : (x : X) → Y x → Set k}
            → ((x : X) → Σ (Y x) λ y → Z x y)
            ≅ (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap-iso = record
  { to = λ f → (proj₁ ∘ f , proj₂ ∘ f)
  ; from = λ { (f , g) x → (f x , g x) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

curry-iso : ∀ {i j k}{X : Set i}{Y : X → Set j}
            (Z : (x : X) → Y x → Set k)
          → ((xy : Σ X Y) → Z (proj₁ xy) (proj₂ xy))
          ≅ ((x : X) → (y : Y x) → Z x y)
curry-iso _ = record
  { to = λ f x y → f (x , y)
  ; from = λ { f (x , y) → f x y }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

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
