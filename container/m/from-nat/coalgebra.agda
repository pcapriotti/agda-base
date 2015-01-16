{-# OPTIONS --without-K #-}
module container.m.from-nat.coalgebra where

open import level
open import sum
open import equality
open import function
open import sets.nat.core
open import sets.nat.struct
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

  abstract
    outL-iso : ∀ i → L i ≅ F L i
    outL-iso i = shift-iso i ·≅ lim-iso i

  inL : F L →ⁱ L
  inL i = invert (outL-iso i)

  outL : L →ⁱ F L
  outL i = apply (outL-iso i)

  in-out : inL ∘ⁱ outL ≡ idⁱ
  in-out = funext λ i → funext λ x → _≅_.iso₁ (outL-iso i) x

  𝓛 : Coalg _
  𝓛 = L , outL

  module _ {ℓ} (𝓩 : Coalg ℓ) where
    private
      Z = proj₁ 𝓩; θ = proj₂ 𝓩

    lim-coalg-iso : Mor 𝓩 𝓛 ≅ ⊤
    lim-coalg-iso = begin
        ( Σ (Z →ⁱ L) λ f → outL ∘ⁱ f ≡ step f )
      ≅⟨ Σ-ap-iso refl≅ eq-lem ⟩
        ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ inL ∘ⁱ step f )
      ≅⟨ Ψ-lem ⟩
        ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ Ψ f  )
      ≅⟨ ( Σ-ap-iso refl≅ λ f → trans≡-iso (ap (λ h₁ → h₁ ∘ⁱ f) (sym in-out)) ) ⟩
        ( Σ (Z →ⁱ L) λ f → f ≡ Ψ f )
      ≅⟨ sym≅ (Σ-ap-iso isom λ _ → refl≅) ⟩
        ( Σ Cone λ c → apply isom c ≡ Ψ (apply isom c) )
      ≅⟨ ( Σ-ap-iso refl≅ λ c → trans≡-iso' (Φ-Ψ-comm c) ) ⟩
        ( Σ Cone λ c → apply isom c ≡ apply isom (Φ c) )
      ≅⟨ sym≅ (Σ-ap-iso refl≅ λ c → iso≡ isom ) ⟩
        ( Σ Cone λ c → c ≡ Φ c )
      ≅⟨ ( Σ-ap-iso refl≅ λ _ → refl≅ ) ⟩
        ( Σ Cone λ { (u , q) → (u , q) ≡ (Φ₀ u , Φ₁ u q) } )
      ≅⟨ (Σ-ap-iso refl≅ λ { (u , q) → sym≅ Σ-split-iso }) ⟩
        ( Σ Cone λ { (u , q) → Σ (u ≡ Φ₀ u) λ p → subst Cone₁ p q ≡ Φ₁ u q } )
      ≅⟨ record
           { to = λ { ((u , q) , p , r) → (u , p) , q , r }
           ; from = λ { ((u , p) , q , r) → (u , q) , p , r }
           ; iso₁ = λ { ((u , q) , p , r) → refl }
           ; iso₂ = λ { ((u , p) , q , r) → refl } } ⟩
        ( Σ (Σ Cone₀ λ u → u ≡ Φ₀ u) λ { (u , p)
        → Σ (Cone₁ u) λ q → subst Cone₁ p q ≡ Φ₁ u q } )
      ≅⟨ sym≅ ( Σ-ap-iso (sym≅ (contr-⊤-iso Fix₀-contr)) λ _ → refl≅ )
         ·≅ ×-left-unit ⟩
        ( Σ (Cone₁ u₀) λ q
        → subst Cone₁ (funext p₀) q ≡ Φ₁ u₀ q )
      ≅⟨ Fix₁-iso ⟩
        ⊤
      ∎
      where
        open ≅-Reasoning

        X₀-contr : ∀ i → contr (X i 0)
        X₀-contr i = ↑-level _ ⊤-contr

        Z→X₀-contr : contr (Z →ⁱ Xⁱ 0)
        Z→X₀-contr = Π-level λ i → Π-level λ _ → X₀-contr i

        Cone₀ : Set _
        Cone₀ = (n : ℕ) → Z →ⁱ Xⁱ n

        Cone₁ : Cone₀ → Set _
        Cone₁ u = (n : ℕ) → πⁱ n ∘ⁱ u (suc n) ≡ u n

        Cone : Set _
        Cone = Σ Cone₀ Cone₁

        isom : Cone ≅ (Z →ⁱ L)
        isom = Limit-univⁱ.univ-iso I Xⁱ πⁱ

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

        u₀ : Cone₀
        u₀ zero = λ _ _ → lift tt
        u₀ (suc n) = step (u₀ n)

        p₀ : ∀ n → u₀ n ≡ Φ₀ u₀ n
        p₀ zero = refl
        p₀ (suc n) = refl

        Fix₀ : Set (ℓ ⊔ la ⊔ lb ⊔ li)
        Fix₀ = Σ Cone₀ λ u → u ≡ Φ₀ u

        Fix₁ : Fix₀ → Set (ℓ ⊔ la ⊔ lb ⊔ li)
        Fix₁ (u , p) = Σ (Cone₁ u) λ q → subst Cone₁ p q ≡ Φ₁ u q

        Fix₀-center : Fix₀
        Fix₀-center = u₀ , funext p₀

        Fix₀-iso : Fix₀ ≅ (∀ i → Z i → X i 0)
        Fix₀-iso = begin
            ( Σ Cone₀ λ u → u ≡ Φ₀ u )
          ≅⟨ ( Σ-ap-iso refl≅ λ u → sym≅ strong-funext-iso ·≅ ℕ-elim-shift ) ⟩
            ( Σ Cone₀ λ u → (u 0 ≡ λ _ _ → lift tt)
                          × (∀ n → u (suc n) ≡ step (u n)) )
          ≅⟨ ( Σ-ap-iso refl≅ λ u → (×-ap-iso (contr-⊤-iso (h↑ Z→X₀-contr _ _)) refl≅)
                                  ·≅ ×-left-unit ) ⟩
            ( Σ Cone₀ λ u → (∀ n → u (suc n) ≡ step (u n)) )
          ≅⟨ Limit-op.lim-contr (λ n → Z →ⁱ Xⁱ n) (λ n → step) ⟩
            (∀ i → Z i → X i 0)
          ∎

        Fix₀-contr : contr Fix₀
        Fix₀-contr = Fix₀-center , contr⇒prop
          (iso-level (sym≅ Fix₀-iso) Z→X₀-contr) _

        Fix₁-iso : Fix₁ Fix₀-center ≅ ⊤
        Fix₁-iso = begin
            ( Σ (Cone₁ u₀) λ q → subst Cone₁ (funext p₀) q ≡ Φ₁ u₀ q )
          ≅⟨ ( Σ-ap-iso refl≅ λ q → sym≅ strong-funext-iso ) ⟩
            ( Σ (Cone₁ u₀) λ q → ∀ n → subst Cone₁ (funext p₀) q n ≡ Φ₁ u₀ q n )
          ≅⟨ ( Σ-ap-iso refl≅ λ q → Π-ap-iso refl≅ λ n
             → sym≅ (trans≡-iso (subst-lem _ _ p₀ q n)) ) ⟩
            ( Σ (Cone₁ u₀) λ q → ∀ n
            → subst₂ (P n) (p₀ (suc n)) (p₀ n) (q n) ≡ Φ₁ u₀ q n )
          ≅⟨ ( Σ-ap-iso refl≅ λ q → ℕ-elim-shift ) ⟩
            ( Σ (Cone₁ u₀) λ q
            → (q 0 ≡ Φ₁ u₀ q 0)
            × (∀ n → q (suc n) ≡ Φ₁ u₀ q (suc n)) )
          ≅⟨ ( Σ-ap-iso refl≅ λ q → ×-ap-iso (contr-⊤-iso (h↑ (h↑ Z→X₀-contr _ _) _ _))
                                             refl≅
                                  ·≅ ×-left-unit ) ⟩
            ( Σ (Cone₁ u₀) λ q
            → ∀ n → q (suc n) ≡ ap step (q n) )
          ≅⟨ Limit-op.lim-contr (λ n → πⁱ n ∘ⁱ u₀ (suc n) ≡ u₀ n) (λ n → ap step) ⟩
            ( πⁱ 0 ∘ⁱ u₀ 1 ≡ u₀ 0 )
          ≅⟨ contr-⊤-iso (h↑ Z→X₀-contr _ _) ⟩
            ⊤
          ∎
          where
            P = λ m x y → πⁱ m ∘ⁱ x ≡ y

            subst-lem₁ : (u v : Cone₀)(p : u ≡ v)(q : Cone₁ u)(n : ℕ)
                       → subst Cone₁ p q n
                       ≡ subst₂ (P n) (funext-inv p (suc n)) (funext-inv p n) (q n)
            subst-lem₁ u .u refl q n = refl

            subst-lem : (u v : Cone₀)(p : ∀ n → u n ≡ v n)(q : Cone₁ u)(n : ℕ)
                      → subst Cone₁ (funext p) q n
                      ≡ subst₂ (P n) (p (suc n)) (p n) (q n)
            subst-lem u v p q n = subst-lem₁ u v (funext p) q n
                                · ap (λ p → subst₂ (P n) (p (suc n)) (p n) (q n))
                                     (_≅_.iso₁ strong-funext-iso p)

        Ψ : (Z →ⁱ L) → (Z →ⁱ L)
        Ψ f = inL ∘ⁱ step f

        Ψ-lem : ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ inL ∘ⁱ step f)
              ≅ ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ Ψ f )
        Ψ-lem = Σ-ap-iso refl≅ λ f → refl≅

        Φ-Ψ-comm : (c : Cone) → Ψ (apply isom c) ≡ apply isom (Φ c)
        Φ-Ψ-comm c = {!!}

        eq-lem : (f : Z →ⁱ L) → (outL ∘ⁱ f ≡ step f)
                              ≅ (inL ∘ⁱ outL ∘ⁱ f ≡ inL ∘ⁱ step f)
        eq-lem f = iso≡ ( Π-ap-iso refl≅ λ i
                        → Π-ap-iso refl≅ λ _
                        → sym≅ (outL-iso i) )

    lim-terminal : contr (Mor 𝓩 𝓛)
    lim-terminal = iso-level (sym≅ lim-coalg-iso) ⊤-contr
