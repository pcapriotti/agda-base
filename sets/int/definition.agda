{-# OPTIONS --without-K #-}

module sets.int.definition where

open import sum
open import equality
open import function
open import sets.nat.core
open import hott.hlevel

private
  data Z : Set where
    mk-int : ℕ → ℕ → Z

ℤ : Set
ℤ = Z

_[-]_ : ℕ → ℕ → ℤ
_[-]_ = mk-int

postulate
  eq-ℤ : (n m d : ℕ) → n [-] m ≡ (d + n) [-] (d + m)
  hℤ : h 2 ℤ

IsAlg-ℤ : ∀ {i} → Set i → Set _
IsAlg-ℤ X = Σ (ℕ → ℕ → X) λ f
          → (∀ n m d → f n m ≡ f (d + n) (d + m))

aℤ : IsAlg-ℤ ℤ
aℤ = _[-]_ , eq-ℤ

map-Alg-ℤ : ∀ {i j}{X : Set i}{Y : Set j}
          → (X → Y) → IsAlg-ℤ X → IsAlg-ℤ Y
map-Alg-ℤ {X = X}{Y} h (f , u) = (g , v)
  where
    g : ℕ → ℕ → Y
    g n m = h (f n m)

    v : ∀ n m d → g n m ≡ g (d + n) (d + m)
    v n m d = ap h (u n m d)

map-Alg-ℤ-id : ∀ {i}{X : Set i}(aX : IsAlg-ℤ X)
             → map-Alg-ℤ (λ x → x) aX ≡ aX
map-Alg-ℤ-id aX = unapΣ (refl ,
  funext λ n → funext λ m → funext λ d → ap-id _)

map-Alg-ℤ-hom : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
     → (f : Y → Z)(g : X → Y)(aX : IsAlg-ℤ X)
     → map-Alg-ℤ (f ∘' g) aX
     ≡ map-Alg-ℤ f (map-Alg-ℤ g aX)
map-Alg-ℤ-hom f g aX = unapΣ (refl , funext λ n → funext λ m → funext λ d
  → sym (ap-hom g f _))

Hom-ℤ : ∀ {i j}{X : Set i}{Y : Set j}
      → IsAlg-ℤ X → IsAlg-ℤ Y → Set _
Hom-ℤ {X = X}{Y} aX aY = Σ (X → Y) λ h → map-Alg-ℤ h aX ≡ aY

id-ℤ : ∀ {i}{X : Set i}(aX : IsAlg-ℤ X) → Hom-ℤ aX aX
id-ℤ aX = (λ x → x) , map-Alg-ℤ-id aX

_⋆ℤ_ : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
     → {aX : IsAlg-ℤ X}{aY : IsAlg-ℤ Y}{aZ : IsAlg-ℤ Z}
     → Hom-ℤ aY aZ → Hom-ℤ aX aY → Hom-ℤ aX aZ
_⋆ℤ_ {aX = aX} (f , u) (g , v) = f ∘' g , map-Alg-ℤ-hom f g aX · ap (map-Alg-ℤ f) v · u

module _ {i}{X : Set i}(hX : h 2 X)(aX : IsAlg-ℤ X) where

  elim-ℤ : ℤ → X
  elim-ℤ (mk-int n n') = proj₁ aX n n'

  postulate elim-β-ℤ : ∀ n m d → ap elim-ℤ (eq-ℤ n m d) ≡ proj₂ aX n m d

  elim-Alg-β-ℤ : map-Alg-ℤ elim-ℤ aℤ ≡ aX
  elim-Alg-β-ℤ = unapΣ (refl , funext λ n → funext λ m → funext λ d → elim-β-ℤ n m d)

  elim-Alg-ℤ : Hom-ℤ aℤ aX
  elim-Alg-ℤ = elim-ℤ , elim-Alg-β-ℤ

  postulate univ-ℤ : (h : Hom-ℤ aℤ aX) → elim-Alg-ℤ ≡ h

  Hom-ℤ-contr : contr (Hom-ℤ aℤ aX)
  Hom-ℤ-contr = elim-Alg-ℤ , univ-ℤ

elim-prop-ℤ : ∀ {i}{X : ℤ → Set i} → (∀ n → h 1 (X n))
            → (f : ∀ n m → X (n [-] m))
            → ∀ n → X n
elim-prop-ℤ {X = X} hX f n = subst X (i-β₀ n) (proj₂ (s₀ n))
  where
    Y : Set _
    Y = Σ ℤ X

    hY : h 2 Y
    hY = Σ-hlevel hℤ λ n → h↑ (hX n)

    aY : IsAlg-ℤ Y
    aY = (λ n m → (n [-] m , f n m))
       , (λ n m d → unapΣ (eq-ℤ n m d , h1⇒prop (hX ((d + n) [-] (d + m))) _ _))

    pY : Hom-ℤ aY aℤ
    pY = proj₁ , unapΣ (refl , h1⇒prop
      (Π-hlevel λ n → Π-hlevel λ m → Π-hlevel λ p → hℤ _ _) _ _)

    s : Hom-ℤ aℤ aY
    s = elim-Alg-ℤ hY aY

    s₀ : ℤ → Y
    s₀ = proj₁ s

    i-β₀ : ∀ n → proj₁ (s₀ n) ≡ n
    i-β₀ n = ap (λ f → proj₁ f n)
      (contr⇒prop (Hom-ℤ-contr hℤ aℤ) (pY ⋆ℤ s) (id-ℤ aℤ))
