{-# OPTIONS --without-K #-}
module hott.truncation.equality where

open import sum
open import equality
open import function.extensionality
open import function.isomorphism
open import function.overloading
open import sets.nat
open import hott.equivalence
open import hott.level.core
open import hott.level.closure
open import hott.truncation.core

private
  module _ {i}{X : Set i}(n-1 : ℕ) where
    n : ℕ
    n = suc n-1

    Trunc-dep-iso₂ : ∀ {j} (Z : Trunc n X → Trunc n X → Set j)
                   → ((c c' : Trunc n X) → h n (Z c c'))
                   → ((c c' : Trunc n X) → Z c c')
                   ≅ ((x y : X) → Z [ x ] [ y ])
    Trunc-dep-iso₂ Z hZ = begin
        ((c c' : Trunc n X) → Z c c')
      ≅⟨ (Π-ap-iso refl≅ λ c → Trunc-dep-iso n (Z c) (hZ c)) ⟩
        ((c : Trunc n X)(y : X) → Z c [ y ])
      ≅⟨ Trunc-dep-iso n (λ c → (y : X) → Z c [ y ]) (λ c → Π-level λ y → hZ c [ y ]) ⟩
        ((x y : X) → Z [ x ] [ y ])
      ∎
      where open ≅-Reasoning

    abstract
      P₀ : X → X → Type i (n-1)
      P₀ x y = Trunc (n-1) (x ≡ y) , Trunc-level n-1

      r₀ : (x : X) → proj₁ (P₀ x x)
      r₀ x = [ refl ]

      abstract
        P-iso' : (Trunc n X → Trunc n X → Type i (n-1))
               ≅ (X → X → Type i (n-1))
        P-iso' = Trunc-dep-iso₂ (λ _ _ → Type i (n-1))
                               (λ _ _ → type-level)

        P-iso-we : weak-equiv (λ (Z : Trunc n X → Trunc n X → Type i (n-1)) x y → Z [ x ] [ y ])
        P-iso-we = proj₂ (≅⇒≈ P-iso')

      P-iso : (Trunc n X → Trunc n X → Type i (n-1))
            ≅ (X → X → Type i (n-1))
      P-iso = ≈⇒≅ ((λ Z x y → Z [ x ] [ y ]) , P-iso-we)

      P : Trunc n X → Trunc n X → Type i (n-1)
      P = _≅_.from P-iso P₀

      P-β' : (λ x y → P [ x ] [ y ]) ≡ P₀
      P-β' = _≅_.iso₂ P-iso P₀

      P-β : (x y : X) → P [ x ] [ y ] ≡ P₀ x y
      P-β x y = funext-inv (funext-inv P-β' x) y

      r : (c : Trunc n X) → proj₁ (P c c)
      r = Trunc-dep-elim n (λ c → proj₁ (P c c)) (λ c → h↑ (proj₂ (P c c))) λ x
        → subst proj₁ (sym (P-β x x)) (r₀ x)

    abstract
      P-elim-iso : (Z : Trunc n X → Trunc n X → Type i (n-1))
                 → ((c c' : Trunc n X) → proj₁ (P c c') → proj₁ (Z c c'))
                 ≅ ((c : Trunc n X) → proj₁ (Z c c))
      P-elim-iso Z = begin
          ((c c' : Trunc n X) → proj₁ (P c c') → proj₁ (Z c c'))
        ≅⟨ Trunc-dep-iso₂ (λ c c' → proj₁ (P c c') → proj₁ (Z c c'))
                          (λ c c' → Π-level λ p → h↑ (proj₂ (Z c c'))) ⟩
          ((x y : X) → proj₁ (P [ x ] [ y ]) → proj₁ (Z [ x ] [ y ]))
        ≅⟨ ( Π-ap-iso refl≅ λ x
           → Π-ap-iso refl≅ λ y
           → Π-ap-iso (≡⇒≅ (ap proj₁ (P-β x y))) λ _
           → refl≅ ) ⟩
          ((x y : X) → Trunc (n-1) (x ≡ y) → proj₁ (Z [ x ] [ y ]))
        ≅⟨ ( Π-ap-iso refl≅ λ x
           → Π-ap-iso refl≅ λ y
           → Trunc-elim-iso (n-1) (x ≡ y) _ (proj₂ (Z [ x ] [ y ])) ) ⟩
          ((x y : X) → x ≡ y → proj₁ (Z [ x ] [ y ]))
        ≅⟨ ( Π-ap-iso refl≅ λ x → sym≅ J-iso ) ⟩
          ((x : X) → proj₁ (Z [ x ] [ x ]))
        ≅⟨ sym≅ (Trunc-dep-iso n (λ c → proj₁ (Z c c)) (λ c → h↑ (proj₂ (Z c c)))) ⟩
          ((c : Trunc n X) → proj₁ (Z c c))
        ∎
        where open ≅-Reasoning

    Eq : Trunc n X → Trunc n X → Type i (n-1)
    Eq c c' = (c ≡ c') , Trunc-level n c c'

    abstract
      f₀ : (c c' : Trunc n X) → proj₁ (P c c') → c ≡ c'
      f₀ = _≅_.from (P-elim-iso Eq) (λ _ → refl)

    abstract
      f : (c c' : Trunc n X) → proj₁ (P c c') → c ≡ c'
      f c c' p = f₀ c c' p · sym (f₀ c' c' (r c'))

      f-β : (c : Trunc n X) → f c c (r c) ≡ refl
      f-β c = left-inverse (f₀ c c (r c))

    g : (c c' : Trunc n X) → c ≡ c' → proj₁ (P c c')
    g c .c refl = r c

--    α : (c c' : Trunc n X)(p : proj₁ (P c c')) → g c c' (f c c' p) ≡ p
--    α = _≅_.from (P-elim-dep-iso Z) λ c → ap (g c c) (f-β c)
--      where
--        Z : (c c' : Trunc n X) → proj₁ (P c c') → Type i (n-1)
--        Z c c' p = (g c c' (f c c' p) ≡ p) , h↑ (proj₂ (P c c')) _ _

    β : (c c' : Trunc n X)(q : c ≡ c') → f c c' (g c c' q) ≡ q
    β c .c refl = f-β c
