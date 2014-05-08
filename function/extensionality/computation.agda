{-# OPTIONS --without-K #-}
module function.extensionality.computation where

open import equality
open import function.isomorphism
open import function.core
open import function.extensionality.core
open import function.extensionality.proof
open import function.extensionality.strong

funext-inv-hom : {X : Set}{Y : X → Set}
               → {f₁ f₂ f₃ : (x : X) → Y x}
               → (p₁ : f₁ ≡ f₂)
               → (p₂ : f₂ ≡ f₃)
               → funext-inv (p₁ · p₂)
               ≡ (λ x → funext-inv p₁ x · funext-inv p₂ x)
funext-inv-hom refl p₂ = refl

funext-hom : {X : Set}{Y : X → Set}
           → {f₁ f₂ f₃ : (x : X) → Y x}
           → (h₁ : (x : X) → f₁ x ≡ f₂ x)
           → (h₂ : (x : X) → f₂ x ≡ f₃ x)
           → funext (λ x → h₁ x · h₂ x)
           ≡ funext h₁ · funext h₂
funext-hom h₁ h₂ = begin
    funext (λ x → h₁ x · h₂ x)
  ≡⟨ sym (ap funext (ap₂ (λ u v x → u x · v x)
                         (_≅_.iso₁ strong-funext-iso h₁)
                         (_≅_.iso₁ strong-funext-iso h₂))) ⟩
    funext (λ x → funext-inv (funext h₁) x · funext-inv (funext h₂) x)
  ≡⟨ sym (ap funext (funext-inv-hom (funext h₁) (funext h₂))) ⟩
    funext (funext-inv (funext h₁ · funext h₂))
  ≡⟨ _≅_.iso₂ strong-funext-iso (funext h₁ · funext h₂) ⟩
    funext h₁ · funext h₂
  ∎
  where open ≡-Reasoning

funext-inv-ap : {X : Set}{Y : X → Set}{Z : X → Set}
              → (g : {x : X} → Y x → Z x)
              → {f₁ f₂ : (x : X) → Y x}
              → (p : f₁ ≡ f₂)
              → funext-inv (ap (_∘'_ g) p)
              ≡ ((λ x → ap g (funext-inv p x)))
funext-inv-ap g refl = refl

funext-ap : {X : Set}{Y : X → Set}{Z : X → Set}
          → (g : {x : X} → Y x → Z x)
          → {f₁ f₂ : (x : X) → Y x}
          → (h : (x : X) → f₁ x ≡ f₂ x)
          → funext (λ x → ap g (h x))
          ≡ ap (_∘'_ g) (funext h)
funext-ap g h = begin
    funext (λ x → ap g (h x))
  ≡⟨ sym (ap funext (ap (λ h x → ap g (h x))
                    (_≅_.iso₁ strong-funext-iso h))) ⟩
    funext (λ x → ap g (funext-inv (funext h) x))
  ≡⟨ ap funext (sym (funext-inv-ap g (funext h))) ⟩
    funext (funext-inv (ap (_∘'_ g) (funext h)))
  ≡⟨ _≅_.iso₂ strong-funext-iso _ ⟩
    ap (_∘'_ g) (funext h)
  ∎
  where open ≡-Reasoning
