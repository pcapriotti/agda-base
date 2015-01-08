{-# OPTIONS --without-K #-}
module container.m.from-nat.core where

open import level
open import sum
open import equality
open import function
open import container.core
open import sets.nat.core
open import sets.nat.struct
open import sets.unit
open import hott.level

module Limit {i} (X : ℕ → Set i)
                 (π : (n : ℕ) → X (suc n) → X n) where
  L : Set _
  L = Σ ((n : ℕ) → X n) λ x
    → (∀ n → π n (x (suc n)) ≡ x n)

  p : (n : ℕ) → L → X n
  p n (x , q) = x n

  β : (n : ℕ) → ∀ x → π n (p (suc n) x) ≡ p n x
  β n (x , q) = q n

module Limit-univ {i j}{Z : Set i}
                  (X : Z → ℕ → Set j)
                  (π : (z : Z)(n : ℕ) → X z (suc n) → X z n) where
  open module WithZ (z : Z) = Limit (X z) (π z)

  univ-iso : ( Σ ((n : ℕ)(z : Z) → X z n) λ u
             → ∀ n z → π z n (u (suc n) z) ≡ u n z )
           ≅ ((z : Z) → L z)
  univ-iso = begin
      ( Σ ((n : ℕ)(z : Z) → X z n) λ u
      → ∀ n z → π z n (u (suc n) z) ≡ u n z )
    ≅⟨ (Σ-ap-iso Π-comm-iso λ u → Π-comm-iso) ⟩
      ( Σ ((z : Z)(n : ℕ) → X z n) λ u
      → ∀ z n → π z n (u z (suc n)) ≡ u z n )
    ≅⟨ sym≅ ΠΣ-swap-iso ⟩
      ((z : Z) → L z)
    ∎
    where open ≅-Reasoning

module Limit-op {i} (X : ℕ → Set i)
                    (ρ : (n : ℕ) → X n → X (suc n)) where
  L : Set _
  L = Σ ((n : ℕ) → X n) λ x
    → (∀ n → x (suc n) ≡ ρ n (x n))

  module _ (χ : (x₀ : X 0)
              → contr ( Σ ((n : ℕ) → X n) λ x
              → (x₀ ≡ x 0)
              × (∀ n → ρ n (x n) ≡ x (suc n)) ) ) where
    lim-contr' : L ≅ X 0
    lim-contr' = begin
        L
      ≅⟨ sym≅ ( Σ-ap-iso refl≅ λ x → Π-ap-iso refl≅ λ n → sym≡-iso _ _ ) ⟩
        ( Σ ((n : ℕ) → X n) λ x
        → (∀ n → ρ n (x n) ≡ x (suc n)) )
      ≅⟨ sym≅ ( Σ-ap-iso refl≅ λ x → ×-left-unit ) ⟩
        ( Σ ((n : ℕ) → X n) λ x
        → Σ ⊤ λ _
        → (∀ n → ρ n (x n) ≡ x (suc n)) )
      ≅⟨ sym≅ ( Σ-ap-iso refl≅ λ x
              → Σ-ap-iso (contr-⊤-iso (singl-contr' (x 0))) λ _
              → refl≅ ) ⟩
        ( Σ ((n : ℕ) → X n) λ x
        → Σ (singleton' (x 0)) λ _
        → (∀ n → ρ n (x n) ≡ x (suc n)) )
      ≅⟨ record
          { to = λ { (x , (z , p) , q) → (z , x , p , q) }
          ; from = λ { (z , x , p , q) → (x , (z , p) , q) }
          ; iso₁ = λ { (x , (z , p) , q) → refl }
          ; iso₂ = λ { (z , x , p , q) → refl } } ⟩
        ( Σ (X 0) λ z
        → Σ ((n : ℕ) → X n) λ x
        → Σ (z ≡ x 0) λ _
        → (∀ n → ρ n (x n) ≡ x (suc n)) )
      ≅⟨ (Σ-ap-iso refl≅ λ z → contr-⊤-iso (χ z)) ·≅ ×-right-unit ⟩
        X 0
      ∎
      where
        open ≅-Reasoning

  lim-contr : L ≅ X 0
  lim-contr = lim-contr' (λ z → ℕ-initial X z ρ)

module Limit-op-simple {i} (X : Set i) where
  module L = Limit-op (λ _ → X) (λ _ x → x)

  lim-contr : L.L ≅ X
  lim-contr = L.lim-contr' ℕ-initial-simple

module Limit-univⁱ
         {ℓ li}(I : Set li)
         (X : ℕ → I → Set ℓ)
         (π : ∀ n → X (suc n) →ⁱ X n) where

  open module WithI (i : I) = Limit (λ n → X n i) (λ n → π n i)

  module _ {ℓ'}{Z : I → Set ℓ'} where
    private
      IZ = Σ I Z

      XZ : IZ → ℕ → Set _
      XZ (i , _) n = X n i

      πZ : (iz : IZ)(n : ℕ) → XZ iz (suc n) → XZ iz n
      πZ (i , _) n = π n i

    univ-iso : ( Σ ((n : ℕ) → Z →ⁱ X n) λ f
               → (∀ n → π n ∘ⁱ f (suc n) ≡ f n) )
             ≅ (Z →ⁱ L)
    univ-iso = begin
       ( Σ ((n : ℕ)(i : I) → Z i → X n i) λ f
       → ∀ n → (λ i z → π n i (f (suc n) i z)) ≡ f n )
     ≅⟨ ( Σ-ap-iso refl≅ λ f → Π-ap-iso refl≅ λ n → sym≅ funext-isoⁱ ) ⟩
        ( Σ ((n : ℕ)(i : I) → Z i → X n i) λ f
        → ∀ n i z → π n i (f (suc n) i z) ≡ f n i z )
     ≅⟨ ( Σ-ap-iso ( Π-ap-iso refl≅ λ n
                   → sym≅ (curry-iso (λ i z → X n i))) λ f
         → Π-ap-iso refl≅ λ n
         → sym≅ (curry-iso (λ i z → π n i (f (suc n) i z) ≡ f n i z)) ) ⟩
       ( Σ ((n : ℕ)(iz : IZ) → XZ iz n) λ f
       → (∀ n iz → πZ iz n (f (suc n) iz) ≡ f n iz) )
     ≅⟨ Limit-univ.univ-iso XZ πZ ⟩
       ((iz : IZ) → L (proj₁ iz))
     ≅⟨ curry-iso (λ i z → L i) ⟩
       (Z →ⁱ L)
     ∎
     where
       open ≅-Reasoning

module F-Limit {ℓ li la lb} (c : Container li la lb)
               (X : Container.I c → ℕ → Set ℓ)
               (π : ∀ i → (n : ℕ) → X i (suc n) → X i n) where
  open Container c
  private
    open module WithI (i : I) = Limit (X i) (π i)

    X' : I → ℕ → Set _
    X' i n = F (λ i → X i n) i

    π' : ∀ i n → X' i (suc n) → X' i n
    π' i n = imap (λ i → π i n) i

    open module WithI' (i : I) = Limit (X' i) (π' i)
      using () renaming (L to L')

  lim-iso : ∀ i → L' i ≅ F L i
  lim-iso i = begin
      ( Σ ((n : ℕ) → F (λ i → X i n) i) λ w
      → (∀ n → imap (λ i → π i n) i (w (suc n)) ≡ w n) )
    ≅⟨ ( Σ-ap-iso ΠΣ-swap-iso λ w → Π-ap-iso refl≅ λ n → sym≅ Σ-split-iso ) ⟩
      ( Σ (Σ (ℕ → A i) λ a → ((n : ℕ) → (b : B (a n)) → X (r b) n)) λ { (a , u)
      → ∀ n
      → Σ (a (suc n) ≡ a n) λ q
      → subst (λ a → (b : B a) → X (r b) n) q
              (λ b → π (r b) n (u (suc n) b)) ≡ u n } )
    ≅⟨ ( Σ-ap-iso refl≅ λ { (a , u) → ΠΣ-swap-iso } ) ⟩
      ( Σ (Σ (ℕ → A i) λ a → ((n : ℕ) → (b : B (a n)) → X (r b) n)) λ { (a , u)
      → Σ (∀ n → a (suc n) ≡ a n) λ q
      → ∀ n → subst (λ a → (b : B a) → X (r b) n) (q n)
                (λ b → π (r b) n (u (suc n) b)) ≡ u n } )
    ≅⟨ record
         { to = λ { ((a , u) , q , z) → ((a , q) , u , z) }
         ; from = λ { ((a , q) , u , z) → ((a , u) , q , z) }
         ; iso₁ = λ { ((a , u) , q , z) → refl }
         ; iso₂ = λ { ((a , q) , u , z) → refl } } ⟩
      ( Σ (Σ (ℕ → A i) λ a → ∀ n → a (suc n) ≡ a n) λ { (a , q)
      → Σ ((n : ℕ) → (b : B (a n)) → X (r b) n) λ u
      → ∀ n → subst (λ a → (b : B a) → X (r b) n) (q n)
                (λ b → π (r b) n (u (suc n) b)) ≡ u n } )
    ≅⟨ sym≅ ( Σ-ap-iso (sym≅ (Limit-op-simple.lim-contr (A i))) λ a → refl≅ ) ⟩
      ( Σ (A i) λ a
      → Σ ((n : ℕ) → (b : B a) → X (r b) n) λ u
      → ∀ n → (λ b → π (r b) n (u (suc n) b)) ≡ u n )
    ≅⟨ ( Σ-ap-iso refl≅ λ a
        → Σ-ap-iso refl≅ λ u
        → Π-ap-iso refl≅ λ n
        → sym≅ strong-funext-iso ) ⟩
      ( Σ (A i) λ a
      → Σ ((n : ℕ) → (b : B a) → X (r b) n) λ u
      → ∀ n b → π (r b) n (u (suc n) b) ≡ u n b )
    ≅⟨ ( Σ-ap-iso refl≅ λ a
       → Limit-univ.univ-iso (λ b n → X (r b) n) (λ b n → π (r b) n) ) ⟩
      F L i
    ∎
    where
      open ≅-Reasoning

module Limit-shift {ℓ} (X : ℕ → Set ℓ)
                       (π : (n : ℕ) → X (suc n) → X n) where
  open Limit X π

  X' : ℕ → Set ℓ
  X' n = X (suc n)

  π' : (n : ℕ) → X' (suc n) → X' n
  π' n = π (suc n)

  open Limit X' π' using ()
    renaming (L to L')

  shift-iso : L ≅ L'
  shift-iso = begin
      ( Σ ((n : ℕ) → X n) λ x
      → ∀ n → π n (x (suc n)) ≡ x n )
    ≅⟨ (Σ-ap-iso ℕ-elim-shift λ _ → ℕ-elim-shift) ⟩
      ( Σ (X 0 × ((n : ℕ) → X (suc n))) λ { (x₀ , y)
      → ((π 0 (y 0) ≡ x₀) × (∀ n → π (suc n) (y (suc n)) ≡ y n)) } )
    ≅⟨ record
         { to = λ { ((x₀ , y) , (q₀ , q)) → (y , (x₀ , q₀) , q) }
         ; from = λ { (y , (x₀ , q₀) , q) → ((x₀ , y) , (q₀ , q)) }
         ; iso₁ = λ { ((x₀ , y) , (q₀ , q)) → refl }
         ; iso₂ = λ { (y , (x₀ , q₀) , q) → refl } } ⟩
      ( Σ ((n : ℕ) → X (suc n)) λ y
      → Σ (singleton (π 0 (y 0))) λ _
      → (∀ n → π (suc n) (y (suc n)) ≡ y n) )
    ≅⟨ ( Σ-ap-iso refl≅ λ y
       → (Σ-ap-iso (contr-⊤-iso (singl-contr _)) λ _ → refl≅)
       ·≅ ×-left-unit ) ⟩
      ( Σ ((n : ℕ) → X (suc n)) λ x
      → ∀ n → π (suc n) (x (suc n)) ≡ x n )
    ∎
    where
      open ≅-Reasoning
