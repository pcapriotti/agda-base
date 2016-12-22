{-# OPTIONS --without-K #-}
open import container.core

module container.w.fibration
  {li la lb}(c : Container li la lb) where

open import sum
open import equality
open import function
open import container.w.core
open import container.w.algebra c
open import hott.level

open Container c

AlgFib : ∀ ℓ → Set _
AlgFib ℓ = Σ ((i : I) → W c i → Set ℓ) λ P
         → (∀ i x → ((b : B (proj₁ x)) → P (r b) (proj₂ x b)) → P i (inW c i x))

AlgSection : ∀ {ℓ} (𝓟 : AlgFib ℓ) → Set _
AlgSection (P , θ) = Σ (∀ i x → P i x) λ f
                   → _≡_ {A = ∀ i x → P i (inW c i x)}
                     (λ i x → θ i x (λ b → f (r b) (proj₂ x b)))
                     (λ i x → f i (inW c i x))

alg-total : ∀ {ℓ} → AlgFib ℓ → Alg _
alg-total (P , θ) = X , ψ
  where
    X : I → Set _
    X i = Σ (W c i) (P i)

    ψ : F X →ⁱ X
    ψ i (a , u) = inW c i (a , λ b → proj₁ (u b))
                , θ i (a , λ b → proj₁ (u b)) (λ b → proj₂ (u b))

module _ {ℓ} (𝓟 : AlgFib ℓ) where
  private 𝓧 = alg-total 𝓟
  open Σ 𝓟 renaming (proj₁ to P ; proj₂ to θ)
  open Σ (alg-total 𝓟) renaming (proj₁ to X ; proj₂ to ψ)

  section : AlgSection 𝓟
  section = f₀ , refl
    where
      f₀ : ∀ i x → P i x
      f₀ i (sup a u) = θ i (a , u) (λ b → f₀ (r b) (u b))

  private
    split-lem : ∀ {ℓ'} (Y : I → Set ℓ')
              → (Y →ⁱ X)
              ≅ ( Σ (Y →ⁱ W c) λ g₀
                → ∀ i x → P i (g₀ i x) )
    split-lem Y
      = sym≅ (curry-iso (λ i _ → X i))
      ·≅ ΠΣ-swap-iso
      ·≅ Σ-ap-iso (curry-iso (λ i _ → W c i))
                  (λ g₀ → curry-iso (λ i x → P i (g₀ (i , x))))

  section-mor-iso : Mor 𝓦 𝓧 ≅ AlgSection 𝓟
  section-mor-iso = begin
      ( Σ (W c →ⁱ X) λ f → ψ ∘ⁱ imap f ≡ f ∘ⁱ inW c )
    ≅⟨ Σ-ap-iso (split-lem (W c)) (λ _ → refl≅) ⟩
      ( Σ (Σ (W c →ⁱ W c) λ f₀ → ∀ i → (w : W c i) → P i (f₀ i w)) λ { (f₀ , f₁)
        → _≡_ {A = ∀ i (x : F (W c) i) → X i}
          (λ i x → let x' = imap f₀ i x
                    in (inW c i x' , θ i x' (λ b → f₁ (r b) (proj₂ x b))))
          (λ i x → (f₀ i (inW c i x) , f₁ i (inW c i x))) } )
    ≅⟨ ( Σ-ap-iso refl≅ λ { (f₀ , f₁) → iso≡ (split-lem (F (W c)))
                                      ·≅ sym≅ Σ-split-iso } ) ⟩
      ( Σ (Σ (W c →ⁱ W c) λ f₀ → ∀ i → (w : W c i) → P i (f₀ i w)) λ { (f₀ , f₁)
      → Σ ( _≡_ {A = ∀ i (x : F (W c) i) → W c i}
            (λ i x → inW c i (imap f₀ i x))
            (λ i x → f₀ i (inW c i x)) ) λ eq
      → subst (λ g → ∀ i (x : F (W c) i) → P i (g i x)) eq
            (λ i x → θ i (imap f₀ i x) (λ b → f₁ (r b) (proj₂ x b)))
          ≡ (λ i x → f₁ i (inW c i x)) } )
    ≅⟨ record
          { to = λ { ((f₀ , f₁) , (α₀ , α₁)) → ((f₀ , α₀) , (f₁ , α₁)) }
          ; from = λ { ((f₀ , α₀) , (f₁ , α₁)) → ((f₀ , f₁) , (α₀ , α₁)) }
          ; iso₁ = λ { ((f₀ , f₁) , (α₀ , α₁)) → refl }
          ; iso₂ = λ { ((f₀ , α₀) , (f₁ , α₁)) → refl } } ⟩
      ( Σ ( Σ (∀ i → W c i → W c i) λ f₀
          → ( _≡_ {A = ∀ i (x : F (W c) i) → W c i}
              (λ i x → inW c i (imap f₀ i x))
              (λ i x → f₀ i (inW c i x)) ) ) λ { (f₀ , eq)
      → Σ (∀ i w → P i (f₀ i w)) λ f₁
      → subst (λ g → ∀ i (x : F (W c) i) → P i (g i x)) eq
            (λ i x → θ i (imap f₀ i x) (λ b → f₁ (r b) (proj₂ x b)))
          ≡ (λ i x → f₁ i (inW c i x)) } )
    ≅⟨ sym≅ ( Σ-ap-iso (sym≅ (contr-⊤-iso W-initial-W)) λ _ → refl≅ ) ·≅ ×-left-unit ⟩
      ( Σ (∀ i w → P i w) λ f₁
      → (λ i x → θ i x (λ b → f₁ (r b) (proj₂ x b)))
      ≡ (λ i x → f₁ i (inW c i x)) )
    ∎
    where
      open ≅-Reasoning

  W-section-contr : contr (AlgSection 𝓟)
  W-section-contr = iso-level section-mor-iso (W-initial 𝓧)
