{-# OPTIONS --without-K #-}
module sets.nat.struct where

open import level
open import sum
open import equality
open import function
open import container.core
open import container.w
open import sets.empty
open import sets.unit
open import sets.nat.core
open import sets.fin
open import sets.vec.dependent
open import hott.level

ℕ-c : Container lzero lzero lzero
ℕ-c = record
  { I = ⊤
  ; A = λ _ → Fin 2
  ; B = ⊥ ∷∷ ⊤ ∷∷ ⟦⟧
  ; r = λ _ → tt }

open Container ℕ-c

ℕ-algebra-iso : (⊤ {lzero} ⊎ ℕ) ≅ ℕ
ℕ-algebra-iso = record
  { to = λ { (inj₁ _) → zero ; (inj₂ n) → suc n }
  ; from = λ { zero → inj₁ tt ; (suc n) → inj₂ n }
  ; iso₁ = λ { (inj₁ _) → refl ; (inj₂ n) → refl }
  ; iso₂ = λ { zero → refl ; (suc n) → refl } }

private
  inℕ : F (λ _ → ℕ) tt → ℕ
  inℕ (zero , u) = 0
  inℕ (suc zero , u) = suc (u tt)
  inℕ (suc (suc ()) , u)

ℕ-struct-iso : ℕ ≅ W ℕ-c tt
ℕ-struct-iso = iso f g α β
  where
    f : ℕ → W ℕ-c tt
    f 0 = sup (# 0) (λ ())
    f (suc n) = sup (# 1) (λ _ → f n)

    g : W ℕ-c tt → ℕ
    g = fold ℕ-c (λ i → inℕ) tt

    α : (n : ℕ) → g (f n) ≡ n
    α zero = refl
    α (suc n) = ap suc (α n)

    β : (n : W ℕ-c tt) → f (g n) ≡ n
    β (sup zero u) = ap (sup zero) (funext λ ())
    β (sup (suc zero) u) = ap (sup (# 1)) (funext (λ x → β (u tt)))
    β (sup (suc (suc ())) u)

private
  F-struct-iso : ∀ {i}(X : ⊤ → Set i) → F X tt ≅ (⊤ ⊎ X tt)
  F-struct-iso X = begin
      ( Σ (A tt) λ a → B a → X tt )
    ≅⟨ sym≅ (⊎-Σ-iso (λ a → B a → X tt)) ⟩
      ( (⊥ → X tt) ⊎ (⊤ → X tt) )
    ≅⟨ ⊎-ap-iso (contr-⊤-iso ⊥-initial) Π-left-unit ⟩
      ( ⊤ ⊎ X tt )
    ∎
    where open ≅-Reasoning

ℕ-initial : ∀ {i} (X : ℕ → Set i)
          → (x₀ : X 0)(f : ∀ n → X n → X (suc n))
          → contr ( Σ ((n : ℕ) → X n) λ x
                  → (x₀ ≡ x 0)
                  × (∀ n → f n (x n) ≡ x (suc n)) )
ℕ-initial X x₀ f = iso-level ℕ-alg-iso (W-section-contr ℕ-c 𝓧)
  where
    ψ : ∀ x → ((b : B (proj₁ x)) → X (proj₂ x b)) → X (inℕ x)
    ψ (zero , u) v = x₀
    ψ (suc zero , u) v = f (u tt) (v tt)
    ψ (suc (suc ()) , u) v

    P : ∀ i (n : W ℕ-c i) → Set _
    P i n = X (invert ℕ-struct-iso n)

    θ : ∀ i x → ((b : B (proj₁ x)) → P tt (proj₂ x b)) → P i (inW ℕ-c i x)
    θ i (a , u) v = ψ (a , invert ℕ-struct-iso ∘' u) v

    𝓧 : AlgFib ℕ-c _
    𝓧 = P , θ

    ℕ-alg-iso : AlgSection ℕ-c 𝓧 ≅
              ( Σ ((n : ℕ) → X n) λ x
              → (x₀ ≡ x 0)
              × (∀ n → f n (x n) ≡ x (suc n)) )
    ℕ-alg-iso = begin
        AlgSection ℕ-c 𝓧
      ≅⟨ ( Σ-ap-iso Π-left-unit λ g → iso≡ Π-left-unit) ⟩
        ( Σ ((w : W ℕ-c tt) → P tt w) λ g
        → ( _≡_ {A = (x : F (W ℕ-c) tt) → P tt (inW ℕ-c tt x)}
            (λ x → θ tt x (λ b → g (proj₂ x b)))
            (λ x → g (inW ℕ-c tt x)) ) )
      ≅⟨ sym≅ ( Σ-ap-iso (Π-ap-iso ℕ-struct-iso λ _ → refl≅) λ g
         → iso≡ (Π-ap-iso (sym≅ (F-ap-iso (λ i → sym≅ ℕ-struct-iso) tt)) λ x
                → refl≅ ) ) ⟩
        ( Σ ((n : ℕ) → X n) λ g
        → ( _≡_ {A = (x : F (λ _ → ℕ) tt) → X (inℕ x)}
            (λ x → ψ x (λ b → g (proj₂ x b)))
            (λ x → g (inℕ x)) ) )
      ≅⟨ ( Σ-ap-iso refl≅ λ g
         → iso≡ (Π-ap-iso (F-struct-iso (λ _ → ℕ)) λ _ → refl≅) ) ⟩
        ( let φ = invert (F-struct-iso (λ _ → ℕ))
        in Σ ((n : ℕ) → X n) λ g
        → ( _≡_ {A = (x : ⊤ ⊎ ℕ) → X (inℕ (φ x))}
            (λ x → ψ (φ x) (λ b → g (proj₂ (φ x) b)))
            (λ x → g (inℕ (φ x))) ) )
      ≅⟨ ( Σ-ap-iso refl≅ λ x → iso≡ ⊎-universal ) ⟩
        ( Σ ((n : ℕ) → X n) λ x
        → ( _≡_ {A = (⊤ → X 0) × ((n : ℕ) → X (suc n))}
            ((λ _ → x₀) , (λ n → f n (x n)))
            ((λ _ → x 0) , (λ n → x (suc n))) ) )
      ≅⟨ ( Σ-ap-iso refl≅ λ x → sym≅ ×-split-iso ) ⟩
        ( Σ ((n : ℕ) → X n) λ x
        → (_≡_ {A = ⊤ → X 0} (λ _ → x₀) (λ _ → x 0))
        × (_≡_ {A = (n : ℕ) → X (suc n)} (λ n → f n (x n)) (λ n → x (suc n))) )
      ≅⟨ ( Σ-ap-iso refl≅ λ x → ×-ap-iso (iso≡ Π-left-unit) (sym≅ strong-funext-iso) ) ⟩
        ( Σ ((n : ℕ) → X n) λ x
        → (x₀ ≡ x 0)
        × (∀ n → f n (x n) ≡ x (suc n)) )
      ∎
      where
        open ≅-Reasoning

ℕ-initial-simple : ∀ {i} {X : Set i} (x₀ : X)
                 → contr ( Σ (ℕ → X) λ x
                         → (x₀ ≡ x 0)
                         × (∀ n → x n ≡ x (suc n)) )
ℕ-initial-simple {X = X} x₀
  = ((λ _ → x₀) , refl , λ _ → refl)
  , (λ u → contr⇒prop (ℕ-initial (λ _ → X) x₀ (λ _ x → x)) _ u)

ℕ-elim-shift : ∀ {i}{X : ℕ → Set i}
             → ((n : ℕ) → X n)
             ≅ ( (X 0) × ((n : ℕ) → X (suc n)) )
ℕ-elim-shift {i}{X} = begin
    ((n : ℕ) → X n)
  ≅⟨ (Π-ap-iso (sym≅ ℕ-algebra-iso) λ _ → refl≅) ⟩
    ((n : ⊤ ⊎ ℕ) → X (apply ℕ-algebra-iso n))
  ≅⟨ ⊎-universal ⟩
    ((⊤ → X 0) × ((n : ℕ) → X (suc n)))
  ≅⟨ ×-ap-iso Π-left-unit refl≅ ⟩
    (X 0 × ((n : ℕ) → X (suc n)))
  ∎
  where
    open ≅-Reasoning
