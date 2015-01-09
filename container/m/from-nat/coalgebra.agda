{-# OPTIONS --without-K #-}
module container.m.from-nat.coalgebra where

open import level
open import sum
open import equality
open import function
open import sets.nat.core
open import sets.unit
open import container.core
open import container.m.from-nat.core
open import hott.level

module _ {li la lb} (c : Container li la lb) where
  open Container c
  open import container.m.coalgebra c

  Xⁱ : ℕ → I → Set (la ⊔ lb)
  Xⁱ zero = λ _ → ↑ _ ⊤
  Xⁱ (suc n) = F (Xⁱ n)

  πⁱ : ∀ n → Xⁱ (suc n) →ⁱ Xⁱ n
  πⁱ zero = λ _ _ → lift tt
  πⁱ (suc n) = imap (πⁱ n)

  module _ (i : I) where
    X : ℕ → Set (la ⊔ lb)
    X n = Xⁱ n i

    π : (n : ℕ) → X (suc n) → X n
    π n = πⁱ n i

    open Limit X π public
    open Limit-shift X π public
  open F-Limit c X π public

  pⁱ : (n : ℕ) → L →ⁱ Xⁱ n
  pⁱ n i = p i n

  βⁱ : (n : ℕ) → πⁱ n ∘ⁱ pⁱ (suc n) ≡ pⁱ n
  βⁱ n = funextⁱ (λ i → β i n)

  outL-iso : ∀ i → L i ≅ F L i
  outL-iso i = shift-iso i ·≅ lim-iso i

  inL : F L →ⁱ L
  inL i = invert (outL-iso i)

  outL : L →ⁱ F L
  outL i = apply (outL-iso i)

  𝓛 : Coalg _
  𝓛 = L , outL

  module _ {ℓ} (𝓩 : Coalg ℓ) where
    private
      Z = proj₁ 𝓩; θ = proj₂ 𝓩

    lim-coalg-iso : Mor 𝓩 𝓛 ≅ (∀ i → Z i → X i 0)
    lim-coalg-iso = begin
        ( Σ (Z →ⁱ L) λ f → outL ∘ⁱ f ≡ imap f ∘ⁱ θ )
      ≅⟨ {!!} ⟩
        ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ inL ∘ⁱ imap f ∘ⁱ θ )
      ≅⟨ {!!} ⟩
        ( Σ (Z →ⁱ L) λ f → f ≡ Ψ f )
      ≅⟨ sym≅ (Σ-ap-iso isom λ _ → refl≅) ⟩
        ( Σ Cone λ c → apply isom c ≡ Ψ (apply isom c) )
      ≅⟨ {!!} ⟩
        ( Σ Cone λ c → apply isom c ≡ apply isom (Φ c) )
      ≅⟨ sym≅ (Σ-ap-iso refl≅ λ c → iso≡ isom ) ⟩
        ( Σ Cone λ c → c ≡ Φ c )
      ≅⟨ (Σ-ap-iso refl≅ λ { (u , q) → trans≡-iso' (Φ-β u q) }) ⟩
        ( Σ Cone λ { (u , q) → (u , q) ≡ (Φ₀ u , Φ₁ u q) } )
      ≅⟨ (Σ-ap-iso refl≅ λ { (u , q) → sym≅ Σ-split-iso }) ⟩
        ( Σ Cone λ { (u , q) → Σ (u ≡ Φ₀ u) λ p → subst Cone₁ p q ≡ Φ₁ u q } )
      ≅⟨ {!!} ⟩
        ( Σ (Σ Cone₀ λ u → u ≡ Φ₀ u) λ { (u , p)
        → Σ (Cone₁ u) λ q → subst Cone₁ p q ≡ Φ₁ u q } )
      ≅⟨ {!!} ⟩
        ( Σ (Σ Cone₀ λ u → u ≡ Φ₀ u) λ { (u , p)
        → Σ (Cone₁ u) λ q → subst Cone₁ p q ≡ Φ₁ u q } )
      ≅⟨ {!!} ⟩
        ( Σ ⊤ λ _
        → Σ (Cone₁ u₀) λ q
        → subst Cone₁ (funext p₀) q ≡ Φ₁ u₀ q )
      ≅⟨ {!!} ⟩
        ( Σ (Cone₁ u₀) λ q
        → subst Cone₁ (funext p₀) q ≡ Φ₁ u₀ q )
      ≅⟨ {!!} ⟩
        (∀ i → Z i → X i 0)
      ∎
      where
        open ≅-Reasoning

        Cone₀ : Set _
        Cone₀ = (n : ℕ) → Z →ⁱ Xⁱ n

        Cone₁ : Cone₀ → Set _
        Cone₁ u = (n : ℕ) → πⁱ n ∘ⁱ u (suc n) ≡ u n

        Cone : Set _
        Cone = Σ Cone₀ Cone₁

        isom : Cone ≅ (Z →ⁱ L)
        isom = Limit-univⁱ.univ-iso I Xⁱ πⁱ

        abstract
          Ψ : (Z →ⁱ L) → (Z →ⁱ L)
          Ψ f = inL ∘ⁱ imap f ∘ⁱ θ

          step : ∀ {ly}{Y : I → Set ly} → (Z →ⁱ Y) → (Z →ⁱ F Y)
          step v = imap v ∘ⁱ θ

          Φ₀ : Cone₀ → Cone₀
          Φ₀ u 0 = λ _ _ → lift tt
          Φ₀ u (suc n) = step (u n)

          Φ₁ : (u : Cone₀) → Cone₁ u → Cone₁ (Φ₀ u)
          Φ₁ u q zero = refl
          Φ₁ u q (suc n) = ap step (q n)

          Φ : Cone → Cone
          Φ (u , q) = (Φ₀ u , Φ₁ u q)

          Φ-Ψ-comm : (c : Cone) → Ψ (apply isom c) ≡ apply isom (Φ c)
          Φ-Ψ-comm c = {!!}

          Φ-β : (u : Cone₀)(q : Cone₁ u) → Φ (u , q) ≡ (Φ₀ u , Φ₁ u q)
          Φ-β u q = refl

          u₀ : Cone₀
          u₀ zero = λ _ _ → lift tt
          u₀ (suc n) = step (u₀ n)

          p₀ : ∀ n → u₀ n ≡ Φ₀ u₀ n
          p₀ zero = refl
          p₀ (suc n) = refl

          Φ₀-fix-center : Σ Cone₀ λ u → u ≡ Φ₀ u
          Φ₀-fix-center = u₀ , funext p₀

          Φ₀-fix-iso : (Σ Cone₀ λ u → u ≡ Φ₀ u) ≅ (∀ i → Z i → X i 0)
          Φ₀-fix-iso = begin
              ( Σ Cone₀ λ u → u ≡ Φ₀ u )
            ≅⟨ {!!} ⟩
              ( Σ Cone₀ λ u → ∀ n → u n ≡ Φ₀ u n )
            ≅⟨ {!!} ⟩
              ( Σ Cone₀ λ u → (u 0 ≡ λ _ _ → lift tt)
                            × (∀ n → u (suc n) ≡ step (u n)) )
            ≅⟨ {!!} ⟩
              ( Σ Cone₀ λ u → ∀ n → u (suc n) ≡ step (u n) )
            ≅⟨ Limit-op.lim-contr (λ n → Z →ⁱ Xⁱ n) (λ n → step) ⟩
              (∀ i → Z i → X i 0)
            ∎

          Φ₀-fix-contr : contr (Σ Cone₀ λ u → u ≡ Φ₀ u)
          Φ₀-fix-contr = Φ₀-fix-center , contr⇒prop
            (iso-level (sym≅ Φ₀-fix-iso)
                       (Π-level λ _ → Π-level λ _ → ↑-level _ ⊤-contr)) _

    lim-terminal : contr (Mor 𝓩 𝓛)
    lim-terminal = iso-level (sym≅ lim-coalg-iso)
      (Π-level λ _ → Π-level λ _ → ↑-level _ ⊤-contr)
