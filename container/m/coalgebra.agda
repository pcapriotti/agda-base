{-# OPTIONS --without-K #-}
open import container.core

module container.m.coalgebra {li la lb}
  (c : Container li la lb) where

open import level
open import sum
open import function as F hiding (_∘_ ; module _≅_ ; _≅_ ; iso ; ≅⇒≡)
open import equality
open import hott
------------------------------------------------------------------------------
open Container c

Coalg : ∀ ℓ → Set _
Coalg ℓ = Σ (I → Set ℓ) λ X → X →ⁱ F X

carrier : ∀ {ℓ} → Coalg ℓ → I → Set ℓ
carrier (X , _) = X

IsMor : ∀ {ℓ₁ ℓ₂}(𝓧 : Coalg ℓ₁)(𝓨 : Coalg ℓ₂)
      → (carrier 𝓧 →ⁱ carrier 𝓨) → Set _
IsMor (X , θ) (Y , ψ) f = ψ ∘ⁱ f ≡ imap f ∘ⁱ θ

_⇒_ : ∀ {ℓ₁ ℓ₂} → Coalg ℓ₁ → Coalg ℓ₂ → Set _
𝓧 ⇒ 𝓨 = Σ (carrier 𝓧 →ⁱ carrier 𝓨) (IsMor 𝓧 𝓨)

idf : ∀ {ℓ} → (𝓧 : Coalg ℓ) → 𝓧 ⇒ 𝓧
idf 𝓧 = (λ i x → x) , refl

_∘_ : ∀ {ℓ} → ⦃ 𝓧 𝓨 𝓩 : Coalg ℓ ⦄ → 𝓨 ⇒ 𝓩 → 𝓧 ⇒ 𝓨 → 𝓧 ⇒ 𝓩
(g , coh₁) ∘ (f , coh₂) = g ∘ⁱ f , funextⁱ (λ i x → funext-invⁱ coh₁ i (f i x)
                                   · ap (imap g i) (funext-invⁱ coh₂ i x))

private
  subst-coerce : ∀ {a b} {A : Set a} {B : A → Set b}
                 {x y : A} (p : x ≡ y) {u : B x}
    → subst B p u ≡ coerce (ap B p) u
  subst-coerce refl = refl

  app= : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → f ≡ g
    →(x : A) → f x ≡ g x
  app= p x = ap (λ u → u x) p

  app=-β : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
           (p : ∀ x → f x ≡ g x) (x : A)
    → app= (funext p) x ≡ p x
  app=-β {B = B} p x = helper (funext p) x
                         · app= (F._≅_.iso₁ strong-funext-iso p) x
    where helper : ∀ {f g : ∀ x → B x} (p : f ≡ g) x → app= p x ≡ funext-inv p x
          helper refl x = refl

  abstract
    ua : ∀ {i}{X Y : Set i} → X F.≅ Y → X ≡ Y
    ua = F.≅⇒≡

    coerce-β : ∀ {a} {X Y : Set a} → (e : X F.≅ Y)
      → ∀ x → coerce (ua e) x ≡ apply e x
    coerce-β e x = app= (uni-coherence (≅⇒≈ e)) x

  substⁱ-lemma : ∀ {ℓ} {X Y : I → Set ℓ} {f : X →ⁱ F X} {g : Y →ⁱ F Y}
                → (p : X ≡ Y)
                → (∀ i x → subst (λ Z → F Z i) p (f i x)
                              ≡ g i (subst (λ Z → Z i) p x))
    → subst (λ Z → Z →ⁱ F Z) p f ≡ g
  substⁱ-lemma refl = funextⁱ

  imap-subst : ∀ {ℓ} {X Y : I → Set ℓ} (p : X ≡ Y)
    → imap (λ i → subst (λ Z → Z i) p) ≡ (λ i → subst (λ Z → F Z i) p)
  imap-subst refl = refl

  prop-subst : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A}
               {p : x ≡ y} {u : B x} {v : B y} → prop (B y)
    → subst B p u ≡ v
  prop-subst {p = refl} pr = pr _ _

record _≅_ {ℓ} (𝓧 𝓨 : Coalg ℓ) : Set (lsuc $ ℓ ⊔ li ⊔ la ⊔ lb) where
  constructor iso
  field
    f : 𝓧 ⇒ 𝓨
    g : 𝓨 ⇒ 𝓧
    f-g : f ∘ g ≡ idf 𝓨
    g-f : g ∘ f ≡ idf 𝓧

≅⇒≡ : ∀ {ℓ} {𝓧 𝓨 : Coalg ℓ} → 𝓧 ≅ 𝓨 → 𝓧 ≡ 𝓨
≅⇒≡ {𝓧 = X , θ} {𝓨 = Y , ψ} 𝓧≅𝓨 = unapΣ (π₁≡ , π₂≡)
  where open _≅_ 𝓧≅𝓨
        X≅Y : ∀ i → X i F.≅ Y i
        X≅Y i = F.iso (proj₁ f i) (proj₁ g i)
                      (funext-invⁱ (ap proj₁ g-f) i)
                      (funext-invⁱ (ap proj₁ f-g) i)
        π₁≡ : X ≡ Y
        π₁≡ = funext λ i → ua (X≅Y i)
        π₂≡ : subst (λ Z → Z →ⁱ F Z) π₁≡ θ ≡ ψ
        π₂≡ = substⁱ-lemma π₁≡ λ i x →
                app= (lemma₂ i) _
              · sym (funext-invⁱ (proj₂ f) i x)
              · ap (ψ i) (sym (lemma₁ i x))
          where lemma₁ : ∀ i x → subst (λ Z → Z i) π₁≡ x ≡ proj₁ f i x
                lemma₁ i x = subst-coerce π₁≡
                           · ap (λ u → coerce u x) (app=-β _ i)
                           · coerce-β (X≅Y i) _
                lemma₂ : ∀ i → subst (λ Z → F Z i) π₁≡ ≡ imap (proj₁ f) i
                lemma₂ i = sym $ funext (hmap (λ i x → sym (lemma₁ i x)) i)
                                   · app= (imap-subst π₁≡) i

IsFinal : ∀ {ℓ} → Coalg ℓ → Set _
IsFinal {ℓ} 𝓧 = ∀ (𝓨 : Coalg ℓ) → contr (𝓧 ⇒ 𝓨)

Final : ∀ ℓ → Set _
Final ℓ = Σ (Coalg ℓ) IsFinal

prop-IsFinal : ∀ {ℓ} (𝓧 : Coalg ℓ) → prop (IsFinal 𝓧)
prop-IsFinal 𝓧 = h1⇒prop (Π-level (λ 𝓨 → contr-h1 _))

Final-prop : ∀ {ℓ} → prop (Final ℓ)
Final-prop (𝓧 , IsFinal-𝓧) (𝓨 , IsFinal-𝓨) =
    unapΣ $ 𝓧≡𝓨 , prop-subst {p = 𝓧≡𝓨} (prop-IsFinal 𝓨)
  where 𝓧≡𝓨 : 𝓧 ≡ 𝓨
        𝓧≡𝓨 = ≅⇒≡ $ iso (proj₁ $ IsFinal-𝓧 𝓨) (proj₁ $ IsFinal-𝓨 𝓧)
                         (contr⇒prop (IsFinal-𝓨 𝓨) _ _)
                         (contr⇒prop (IsFinal-𝓧 𝓧) _ _)
