{-# OPTIONS --without-K #-}
open import container.core

module container.w.algebra
  {li la lb}(c : Container li la lb) where

open import sum
open import equality
open import container.w.core
open import function.extensionality
open import function.isomorphism
open import hott.level.core

open Container c

Alg : ∀ ℓ → Set _
Alg ℓ = Σ (I → Set ℓ) λ X → F X →ⁱ X

carrier : ∀ {ℓ} → Alg ℓ → I → Set ℓ
carrier (X , _) = X

IsMor : ∀ {ℓ₁ ℓ₂}(𝓧 : Alg ℓ₁)(𝓨 : Alg ℓ₂)
      → (carrier 𝓧 →ⁱ carrier 𝓨) → Set _
IsMor (X , θ) (Y , ψ) f = ψ ∘ⁱ imap f ≡ f ∘ⁱ θ

Mor : ∀ {ℓ₁ ℓ₂} → Alg ℓ₁ → Alg ℓ₂ → Set _
Mor 𝓧 𝓨 = Σ (carrier 𝓧 →ⁱ carrier 𝓨) (IsMor 𝓧 𝓨)

𝓦 : Alg _
𝓦 = W c , inW c

module _ {ℓ₁ ℓ₂}(𝓧 : Alg ℓ₁)(𝓨 : Alg ℓ₂) where
  private
    X = proj₁ 𝓧; θ = proj₂ 𝓧
    Y = proj₁ 𝓨; ψ = proj₂ 𝓨

  is-mor-transp : {f g : X →ⁱ Y}(p : f ≡ g)
                → (α : IsMor 𝓧 𝓨 f)
                → sym (ap (λ h → ψ ∘ⁱ imap h) p) · α · ap (λ h → h ∘ⁱ θ) p
                ≡ subst (IsMor 𝓧 𝓨) p α
  is-mor-transp {f} {.f} refl α = left-unit α

  MorEq : Mor 𝓧 𝓨 → Mor 𝓧 𝓨 → Set _
  MorEq (f , α) (g , β) = Σ (f ≡ g) λ p
    → sym (ap (λ h → ψ ∘ⁱ imap h) p) · α · ap (λ h → h ∘ⁱ θ) p ≡ β

  MorH : Mor 𝓧 𝓨 → Mor 𝓧 𝓨 → Set _
  MorH (f , α) (g , β) = Σ (∀ i x → f i x ≡ g i x) λ p
    → ∀ i x → sym (ap (ψ i) (hmap p i x)) · funext-invⁱ α i x · p i (θ i x)
            ≡ funext-invⁱ β i x

  mor-eq-h-iso : (f g : Mor 𝓧 𝓨) → MorEq f g ≅ MorH f g
  mor-eq-h-iso (f , α) (g , β) = Σ-ap-iso (sym≅ funext-isoⁱ) λ p → lem f g α β p
    where
      lem : (f g : X →ⁱ Y)(α : IsMor 𝓧 𝓨 f)(β : IsMor 𝓧 𝓨 g)(p : f ≡ g)
          → (sym (ap (λ h → ψ ∘ⁱ imap h) p) · α · ap (λ h → h ∘ⁱ θ) p ≡ β)
          ≅ (∀ i x → sym (ap (ψ i) (hmap (funext-invⁱ p) i x))
                   · funext-invⁱ α i x
                   · funext-invⁱ p i (θ i x)
                   ≡ funext-invⁱ β i x)
      lem f .f α β refl = begin
          (α · refl ≡ β)
        ≅⟨ sym≅ (trans≡-iso (left-unit α)) ⟩
          (α ≡ β)
        ≅⟨ iso≡ (sym≅ funext-isoⁱ) ⟩
          (funext-invⁱ α ≡ funext-invⁱ β)
        ≅⟨ sym≅ ((Π-ap-iso refl≅ λ _ → strong-funext-iso) ·≅ strong-funext-iso) ⟩
          (∀ i x → funext-invⁱ α i x ≡ funext-invⁱ β i x)
        ≅⟨ ( Π-ap-iso refl≅ λ i
            → Π-ap-iso refl≅ λ x
            → trans≡-iso (comp i x) ) ⟩
          (∀ i x → sym (ap (ψ i) (hmap (funext-invⁱ p₀) i x))
                 · funext-invⁱ α i x
                 · refl
                 ≡ funext-invⁱ β i x)
        ∎
        where
          open ≅-Reasoning

          p₀ : f ≡ f
          p₀ = refl

          comp : ∀ i x → sym (ap (ψ i) (hmap (funext-invⁱ (refl {x = f})) i x))
                       · funext-invⁱ α i x
                       · refl
                       ≡ funext-invⁱ α i x
          comp i x = ap (λ q → sym (ap (ψ i) q) · funext-invⁱ α i x · refl)
                        (hmap-id f i x)
                   · left-unit (funext-invⁱ α i x)

  eq-mor-iso : {f g : Mor 𝓧 𝓨} → (f ≡ g) ≅ MorH f g
  eq-mor-iso {f , α} {g , β} = begin
      ((f , α) ≡ (g , β))
    ≅⟨ sym≅ Σ-split-iso ⟩
      (Σ (f ≡ g) λ p → subst (IsMor 𝓧 𝓨) p α ≡ β)
    ≅⟨ (Σ-ap-iso refl≅ λ p → trans≡-iso (is-mor-transp p α)) ⟩
      MorEq (f , α) (g , β)
    ≅⟨ mor-eq-h-iso _ _ ⟩
      MorH (f , α) (g , β)
    ∎
    where
      open ≅-Reasoning

module _ {ℓ} (𝓧 : Alg ℓ) where
  private
    X = proj₁ 𝓧; θ = proj₂ 𝓧

    lem : ∀ {ℓ}{A : Set ℓ}{x y z w : A}
        → (p : x ≡ w) (q : y ≡ x) (r : y ≡ z) (s : z ≡ w)
        → p ≡ sym q · r · s → sym r · q · p ≡ s
    lem p refl refl refl α = α

  W-mor-prop : (f g : Mor 𝓦 𝓧) → f ≡ g
  W-mor-prop (f , α) (g , β) = invert≅ (eq-mor-iso 𝓦 𝓧) (p , p-h)
    where
      p : ∀ i x → f i x ≡ g i x
      p i (sup a u)
        = sym (funext-invⁱ α i (a , u))
        · ap (θ i) (ap (_,_ a) (funext (λ b → p (r b) (u b))))
        · funext-invⁱ β i (a , u)

      p-h : ∀ i x
          → sym (ap (θ i) (hmap p i x))
          · funext-invⁱ α i x
          · p i (inW c i x)
          ≡ funext-invⁱ β i x
      p-h i (a , u) = lem (p i (sup a u))
                          (funext-invⁱ α i (a , u)) _
                          (funext-invⁱ β i (a , u))
                          refl

  W-mor : Mor 𝓦 𝓧
  W-mor = fold c θ , funextⁱ (λ i x → fold-β c θ x)

W-initial : ∀ {ℓ} (𝓧 : Alg ℓ) → contr (Mor 𝓦 𝓧)
W-initial 𝓧 = W-mor 𝓧 , W-mor-prop 𝓧 (W-mor 𝓧)

-- special case of the isomorphism above, with better
-- computational behaviour
W-initial-W : contr (Mor 𝓦 𝓦)
W-initial-W = id-mor , W-mor-prop 𝓦 id-mor
  where
    id-mor : Mor 𝓦 𝓦
    id-mor = (λ i x → x) , refl
