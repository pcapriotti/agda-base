{-# OPTIONS --without-K #-}
module hott.truncation.core where

open import sum
open import equality
open import function.core
open import function.fibration
open import function.extensionality
open import function.isomorphism
open import sets.nat.core
open import hott.equivalence
open import hott.level.core
open import hott.level.closure

module _ {i j i' j'}{A : Set i}{A' : Set i'}
         {B : A → Set j}{B' : A' → Set j'}
         (f : A → A')
         (g : (a : A) → B a → B' (f a)) where
  private
    E E' : Set _
    E = Σ A B
    E' = Σ A' B'

    p : E → A
    p = proj₁

    p' : E' → A'
    p' = proj₁

    t : E → E'
    t (a , b) = (f a , g a b)

  module _ (f-equiv : weak-equiv f)
           (t-equiv : weak-equiv t) where

    private
      φ : A ≅ A'
      φ = ≈⇒≅ (f , f-equiv)

      τ : E ≅ E'
      τ = ≈⇒≅ (t , t-equiv)

      lem : (a : A)(e : E) → (p e ≡ a) ≅ (p' (t e) ≡ f a)
      lem a e = iso≡ φ

    fib-equiv : (a : A) → B a ≅ B' (f a)
    fib-equiv a = sym≅ (fib-iso a) ·≅ Σ-ap-iso τ (lem a) ·≅ fib-iso (f a)

postulate
  Trunc : ∀ {i} → ℕ → Set i → Set i
  Trunc-level : ∀ {i} n {X : Set i} → h n (Trunc n X)
  [_] : ∀ {i n} {X : Set i} → X → Trunc n X

Trunc-ext : ∀ {i j} n (X : Set i)(Y : Set j)
          → (Trunc n X → Y) → X → Y
Trunc-ext n X Y f x = f [ x ]

postulate
  Trunc-univ : ∀ {i j} n (X : Set i)(Y : Set j) → h n Y
             → weak-equiv (Trunc-ext n X Y)

Trunc-elim-iso : ∀ {i j} n (X : Set i)(Y : Set j) → h n Y
               → (Trunc n X → Y) ≅ (X → Y)
Trunc-elim-iso n X Y hY = ≈⇒≅ (Trunc-ext n X Y , Trunc-univ n X Y hY)

Trunc-elim : ∀ {i j} n (X : Set i)(Y : Set j) → h n Y
           → (X → Y) → (Trunc n X → Y)
Trunc-elim n X Y hY = invert (Trunc-elim-iso n X Y hY)

module _ {i j} n {X : Set i} (Y : Trunc n X → Set j)
         (hY : (x : Trunc n X) → h n (Y x))
         (d : (x : X) → Y ([ x ])) where

  private
    Z : Set _
    Z = Σ (Trunc n X) Y

    hZ : h n Z
    hZ = Σ-level (Trunc-level n) hY

    Sec₂ : ∀ {k}{A : Set k} → (A → Trunc n X) → Set _
    Sec₂ {A = A} r = (x : A) → Y (r x)

    Sec : ∀ {k} → Set k → Set _
    Sec A = Σ (A → Trunc n X) Sec₂

    τ : Sec (Trunc n X) ≅ Sec X
    τ = sym≅ ΠΣ-swap-iso ·≅ Trunc-elim-iso n X Z hZ ·≅ ΠΣ-swap-iso

    ψ : (r : Trunc n X → Trunc n X)
      → (Sec₂ r) ≅ Sec₂ (r ∘ [_])
    ψ = fib-equiv {A = Trunc n X → Trunc n X}{A' = X → Trunc n X}{B = Sec₂} {B' = Sec₂}
        (Trunc-ext n X (Trunc n X)) (λ r g x → g [ x ])
        (Trunc-univ n X (Trunc n X) (Trunc-level n))
        (proj₂ (≅⇒≈ τ))

    sec-iso : Sec₂ (λ x → x) ≅ Sec₂ [_]
    sec-iso = ψ (λ x → x)

  Trunc-dep-elim : (x : Trunc n X) → Y x
  Trunc-dep-elim = invert sec-iso d

  Trunc-dep-elim-β : (x : X) → Trunc-dep-elim [ x ] ≡ d x
  Trunc-dep-elim-β = funext-inv (_≅_.iso₂ sec-iso d)
