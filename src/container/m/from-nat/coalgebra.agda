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
open import container.m.from-nat.cone
open import hott.level

module _ {li la lb} (c : Container li la lb) where
  open Container c
  open import container.m.coalgebra c hiding (_≅_; module _≅_)

  Xⁱ : ℕ → I → Set (la ⊔ lb)
  Xⁱ zero = λ _ → ⊤
  Xⁱ (suc n) = F (Xⁱ n)

  πⁱ : ∀ n → Xⁱ (suc n) →ⁱ Xⁱ n
  πⁱ zero = λ _ _ → tt
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
    outL-iso : ∀ i → F L i ≅ L i
    outL-iso i = lim-iso i ·≅ shift-iso i

    outL-lem₀ : (n : ℕ)(i : I)(x : F L i)
              → p i (suc n) (apply≅ (outL-iso i) x) ≡ imap (pⁱ n) i x
    outL-lem₀ n i x = refl

    outL-lem₁' : (n : ℕ)(i : I)(x : F L i)
               → β i (suc n) (apply≅ (outL-iso i) x)
               ≡ subst₂ (λ w₁ w₀ → π i (suc n) w₁ ≡ w₀)
                        (sym (outL-lem₀ (suc n) i x))
                        (sym (outL-lem₀ n i x))
                        (unapΣ (refl , funext λ b → proj₂ (proj₂ x b) n ))
    outL-lem₁' n i x = refl

  inL : F L →ⁱ L
  inL i = apply≅ (outL-iso i)

  outL : L →ⁱ F L
  outL i = invert≅ (outL-iso i)

  in-out : inL ∘ⁱ outL ≡ idⁱ
  in-out = funext λ i → funext λ x → _≅_.iso₂ (outL-iso i) x

  outL-lem₁ : (n : ℕ)(i : I)(x : F L i)
            → β i (suc n) (apply≅ (outL-iso i) x)
            ≡ ap (π i (suc n)) (outL-lem₀ (suc n) i x)
            · unapΣ (refl , funext λ b → proj₂ (proj₂ x b) n)
            · sym (outL-lem₀ n i x)
  outL-lem₁ n i x = outL-lem₁' n i x
                  · subst-lem (outL-lem₀ (suc n) i x) (outL-lem₀ n i x)
                              (unapΣ (refl , funext (λ b → proj₂ (proj₂ x b) n)))
    where
      P : X i (suc (suc n)) → X i (suc n) → Set _
      P y x = π i (suc n) y ≡ x

      subst-lem : {y₁ y₂ : X i (suc (suc n))}{x₁ x₂ : X i (suc n)}
                → (p : y₁ ≡ y₂)(q : x₁ ≡ x₂)
                → (z : P y₂ x₂)
                → subst₂ P (sym p) (sym q) z ≡ ap (π i (suc n)) p · z · sym q
      subst-lem refl refl refl = refl

  𝓛 : Coalg _
  𝓛 = L , outL

  module _ {ℓ} (𝓩 : Coalg ℓ) where
    private
      Z = proj₁ 𝓩; θ = proj₂ 𝓩

    lim-coalg-iso : 𝓩 ⇒ 𝓛 ≅ ⊤
    lim-coalg-iso = begin
        ( Σ (Z →ⁱ L) λ f → outL ∘ⁱ f ≡ step f )
      ≅⟨ Σ-ap-iso refl≅ eq-lem ⟩
        ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ inL ∘ⁱ step f )
      ≅⟨ Ψ-lem ⟩
        ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ Ψ f  )
      ≅⟨ ( Σ-ap-iso refl≅ λ f → trans≡-iso (ap (λ h₁ → h₁ ∘ⁱ f) (sym in-out)) ) ⟩
        ( Σ (Z →ⁱ L) λ f → f ≡ Ψ f )
      ≅⟨ sym≅ (Σ-ap-iso isom λ _ → refl≅) ⟩
        ( Σ Cone λ c → apply≅ isom c ≡ Ψ (apply≅ isom c) )
      ≅⟨ ( Σ-ap-iso refl≅ λ c → trans≡-iso' (Φ-Ψ-comm c) ) ⟩
        ( Σ Cone λ c → apply≅ isom c ≡ apply≅ isom (Φ c) )
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
        open cones c Xⁱ πⁱ 𝓩

        X₀-contr : ∀ i → contr (X i 0)
        X₀-contr i = ⊤-contr

        Z→X₀-contr : contr (Z →ⁱ Xⁱ 0)
        Z→X₀-contr = Π-level λ i → Π-level λ _ → X₀-contr i

        step : ∀ {ly}{Y : I → Set ly} → (Z →ⁱ Y) → (Z →ⁱ F Y)
        step v = imap v ∘ⁱ θ

        Φ₀ : Cone₀ → Cone₀
        Φ₀ u 0 = λ _ _ → tt
        Φ₀ u (suc n) = step (u n)

        Φ₀' : Cone → Cone₀
        Φ₀' (u , q) = Φ₀ u

        Φ₁ : (u : Cone₀) → Cone₁ u → Cone₁ (Φ₀ u)
        Φ₁ u q zero = refl
        Φ₁ u q (suc n) = ap step (q n)

        Φ₁' : (c : Cone) → Cone₁ (Φ₀ (proj₁ c))
        Φ₁' (u , q) = Φ₁ u q

        Φ : Cone → Cone
        Φ (u , q) = (Φ₀ u , Φ₁ u q)

        u₀ : Cone₀
        u₀ zero = λ _ _ → tt
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
            ( Σ Cone₀ λ u → (u 0 ≡ λ _ _ → tt)
                          × (∀ n → u (suc n) ≡ step (u n)) )
          ≅⟨ ( Σ-ap-iso refl≅ λ u → (×-ap-iso (contr-⊤-iso (h↑ Z→X₀-contr _ _)) refl≅)
                                  ·≅ ×-left-unit ) ⟩
            ( Σ Cone₀ λ u → (∀ n → u (suc n) ≡ step (u n)) )
          ≅⟨ Limit-op.lim-contr (λ n → Z →ⁱ Xⁱ n) (λ n → step) ⟩
            (∀ i → Z i → X i 0)
          ∎
          where open ≅-Reasoning

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

            open ≅-Reasoning

        Ψ : (Z →ⁱ L) → (Z →ⁱ L)
        Ψ f = inL ∘ⁱ step f

        Ψ-lem : ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ inL ∘ⁱ step f)
              ≅ ( Σ (Z →ⁱ L) λ f → inL ∘ⁱ outL ∘ⁱ f ≡ Ψ f )
        Ψ-lem = Σ-ap-iso refl≅ λ f → refl≅

        Φ-Ψ-comm₀ : (f : Z →ⁱ L) → ∀ n i z
                  → p i n (Ψ f i z)
                  ≡ Φ₀' (invert≅ isom f) n i z
        Φ-Ψ-comm₀ f 0 i z = h1⇒prop (h↑ (X₀-contr i)) _ _
        Φ-Ψ-comm₀ f (suc n) i z = outL-lem₀ n i (imap f i (θ i z))

        Φ-Ψ-comm₁' : (f : Z →ⁱ L) → ∀ n i z
                    → β i n (Ψ f i z)
                    ≡ ap (π i n) (Φ-Ψ-comm₀ f (suc n) i z)
                    · funext-invⁱ (Φ₁' (invert≅ isom f) n) i z
                    · sym (Φ-Ψ-comm₀ f n i z)
        Φ-Ψ-comm₁' f 0 i z = h1⇒prop (h↑ (h↑ (X₀-contr i)) _ _) _ _
        Φ-Ψ-comm₁' f (suc n) i z = begin
            β i (suc n) (inL i (imap f i (θ i z)))
          ≡⟨ outL-lem₁ n i (imap f i (θ i z)) ⟩
            ( ap (π i (suc n)) (Φ-Ψ-comm₀ f (suc (suc n)) i z)
            · unapΣ (refl , funext λ b → β (r b) n (proj₂ (imap f i (θ i z)) b))
            · sym (Φ-Ψ-comm₀ f (suc n) i z) )
          ≡⟨ ap (λ ω → ap (π i (suc n)) (Φ-Ψ-comm₀ f (suc (suc n)) i z)
                     · ω · sym (Φ-Ψ-comm₀ f (suc n) i z))
                (lem (λ i x → β i n x) i z) ⟩
            ( ap (π i (suc n)) (Φ-Ψ-comm₀ f (suc (suc n)) i z)
            · funext-invⁱ (ap step (funextⁱ (λ i z → β i n (f i z)))) i z
            · sym (Φ-Ψ-comm₀ f (suc n) i z) )
          ∎
          where
            open ≡-Reasoning

            lem' : {u v : L →ⁱ Xⁱ n}(ω : u ≡ v)(i : I)(z : Z i)
                 → unapΣ (refl , funext λ b → funext-invⁱ ω (r b) (proj₂ (imap f i (θ i z)) b))
                 ≡ funext-invⁱ (ap step (funextⁱ (λ i z → funext-invⁱ ω i (f i z)))) i z
            lem' refl i z = begin
                unapΣ (refl , funext λ b → refl)
              ≡⟨ ap (λ ω → unapΣ (refl , ω)) (_≅_.iso₂ strong-funext-iso refl) ⟩
                refl
              ≡⟨ sym (ap (λ ω → funext-invⁱ (ap step ω) i z)
                         (_≅_.iso₂ funext-isoⁱ refl)) ⟩
               funext-invⁱ (ap step (funextⁱ (λ i z → refl))) i z
              ∎
              where
                open ≡-Reasoning

            lem : {u v : L →ⁱ Xⁱ n}(ω : (i : I)(x : L i) → u i x ≡ v i x)(i : I)(z : Z i)
                → unapΣ (refl , funext λ b → ω (r b) (proj₂ (imap f i (θ i z)) b))
                ≡ funext-invⁱ (ap step (funextⁱ (λ i z → ω i (f i z)))) i z
            lem {u}{v} = invert≅ (Π-ap-iso funext-isoⁱ λ ω → refl≅) lem'

        Φ-Ψ-comm₁ : (f : Z →ⁱ L) → ∀ n i z
                   → funext-invⁱ (funextⁱ λ i z → β i n (Ψ f i z)) i z
                   ≡ ap (π i n) (Φ-Ψ-comm₀ f (suc n) i z)
                   · funext-invⁱ (Φ₁' (invert≅ isom f) n) i z
                   · sym (Φ-Ψ-comm₀ f n i z)
        Φ-Ψ-comm₁ f n i z = ap (λ h → h i z)
                                (_≅_.iso₁ funext-isoⁱ (λ i z → β i n (Ψ f i z)))
                          · Φ-Ψ-comm₁' f n i z

        Φ-Ψ-comm' : (f : Z →ⁱ L) → invert≅ isom (Ψ f) ≡ Φ (invert≅ isom f)
        Φ-Ψ-comm' f = Cone-eq (Φ-Ψ-comm₀ f) (Φ-Ψ-comm₁ f)

        Φ-Ψ-comm : (c : Cone) → Ψ (apply≅ isom c) ≡ apply≅ isom (Φ c)
        Φ-Ψ-comm c = sym (_≅_.iso₂ isom (Ψ (apply≅ isom c)))
                   · ap (apply≅ isom)
                        (Φ-Ψ-comm' (apply≅ isom c) · ap Φ (_≅_.iso₁ isom c))

        cone-comp₀ : (f : Z →ⁱ L)(n : ℕ)(i : I)(z : Z i)
                   → proj₁ (invert≅ isom (Ψ f)) n i z
                   ≡ p i n (Ψ f i z)
        cone-comp₀ f n i z = refl

        cone-comp₁ : (f : Z →ⁱ L)(n : ℕ)
                   → proj₂ (invert≅ isom (Ψ f)) n
                   ≡ funextⁱ (λ i z → β i n (Ψ f i z))
        cone-comp₁ f n = refl

        eq-lem : (f : Z →ⁱ L) → (outL ∘ⁱ f ≡ step f)
                              ≅ (inL ∘ⁱ outL ∘ⁱ f ≡ inL ∘ⁱ step f)
        eq-lem f = iso≡ ( Π-ap-iso refl≅ λ i
                        → Π-ap-iso refl≅ λ _
                        → outL-iso i )

        open ≅-Reasoning

    lim-terminal : contr (𝓩 ⇒ 𝓛)
    lim-terminal = iso-level (sym≅ lim-coalg-iso) ⊤-contr
