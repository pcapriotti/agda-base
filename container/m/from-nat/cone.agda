{-# OPTIONS --without-K #-}
module container.m.from-nat.cone where

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
  open import container.m.coalgebra c hiding (_≅_; module _≅_)

  module _ (Xⁱ : ℕ → I → Set (la ⊔ lb))
           (πⁱ : ∀ n → Xⁱ (suc n) →ⁱ Xⁱ n) where

    private
      X : (i : I) → ℕ → Set (la ⊔ lb)
      X i n = Xⁱ n i

      π : (i : I) (n : ℕ) → X i (suc n) → X i n
      π i n = πⁱ n i

    module cones {ℓ} (𝓩 : Coalg ℓ) where
      private
        Z = proj₁ 𝓩; θ = proj₂ 𝓩

      Cone₀ : Set _
      Cone₀ = (n : ℕ) → Z →ⁱ Xⁱ n

      Cone₁ : Cone₀ → Set _
      Cone₁ u = (n : ℕ) → πⁱ n ∘ⁱ u (suc n) ≡ u n

      Cone : Set _
      Cone = Σ Cone₀ Cone₁

      Cone₀-eq-iso : {u₁ u₂ : Cone₀}
                   → ((n : ℕ)(i : I)(z : Z i) → u₁ n i z ≡ u₂ n i z)
                   ≅ (u₁ ≡ u₂)
      Cone₀-eq-iso = Π-ap-iso refl≅ (λ _ → funext-isoⁱ) ·≅ strong-funext-iso

      Cone₁-eq-iso : {u : Cone₀}{q₁ q₂ : Cone₁ u}
                   → ( (n : ℕ)(i : I)(z : Z i)
                     → funext-invⁱ (q₁ n) i z
                     ≡ funext-invⁱ (q₂ n) i z )
                   ≅ (q₁ ≡ q₂)
      Cone₁-eq-iso {u}{q₁}{q₂} = begin
          ( (n : ℕ)(i : I)(z : Z i)
          → funext-invⁱ (q₁ n) i z
          ≡ funext-invⁱ (q₂ n) i z )
        ≅⟨ (Π-ap-iso refl≅ λ n → funext-isoⁱ) ⟩
          ( (n : ℕ) → funext-invⁱ (q₁ n) ≡ funext-invⁱ (q₂ n) )
        ≅⟨ ( Π-ap-iso refl≅ λ n → sym≅ (iso≡ (sym≅ funext-isoⁱ)) ) ⟩
          ( (n : ℕ) → q₁ n ≡ q₂ n )
        ≅⟨ strong-funext-iso ⟩
          (q₁ ≡ q₂)
        ∎
        where
          open ≅-Reasoning

      Cone-eq : {c₁ c₂ : Cone}
              → (p : (n : ℕ)(i : I)(z : Z i)
                   → proj₁ c₁ n i z ≡ proj₁ c₂ n i z)
              → ( (n : ℕ)(i : I)(z : Z i)
                → funext-invⁱ (proj₂ c₁ n) i z
                ≡ ap (π i n) (p (suc n) i z)
                · funext-invⁱ (proj₂ c₂ n) i z
                · sym (p n i z) )
              → c₁ ≡ c₂
      Cone-eq {c₁}{c₂} p α = unapΣ' (p' , α')
        where
          subst-lem : {u₁ u₂ : Cone₀}(p : u₁ ≡ u₂)(q : Cone₁ u₂)
                    → (n : ℕ)(i : I)(z : Z i)
                    → funext-invⁱ (subst Cone₁ (sym p) q n) i z
                    ≡ ap (π i n) (funext-invⁱ (funext-inv p (suc n)) i z)
                    · funext-invⁱ (q n) i z
                    · sym (funext-invⁱ (funext-inv p n) i z)
          subst-lem refl q n i z = sym (left-unit _)

          subst-lem' : {u₁ u₂ : Cone₀}(p : (n : ℕ)(i : I)(z : Z i) → u₁ n i z ≡ u₂ n i z)
                     → (q : Cone₁ u₂)(n : ℕ)(i : I)(z : Z i)
                     → funext-invⁱ (subst Cone₁ (sym (apply Cone₀-eq-iso p)) q n) i z
                     ≡ ap (π i n) (p (suc n) i z)
                     · funext-invⁱ (q n) i z
                     · sym (p n i z)
          subst-lem' {u₁}{u₂} p q n i z = subst ( λ p₁
            → funext-invⁱ (subst Cone₁ (sym (apply Cone₀-eq-iso p)) q n) i z
            ≡ ap (π i n) (p₁ (suc n) i z) · funext-invⁱ (q n) i z · sym (p₁ n i z) )
              (_≅_.iso₁ Cone₀-eq-iso p) (subst-lem (apply Cone₀-eq-iso p) q n i z)

          p' : proj₁ c₁ ≡ proj₁ c₂
          p' = apply Cone₀-eq-iso p

          α' : proj₂ c₁ ≡ subst Cone₁ (sym p') (proj₂ c₂)
          α' = apply Cone₁-eq-iso λ n i z
             → α n i z
             · sym (subst-lem' p (proj₂ c₂) n i z)

          unapΣ' : ∀ {i j}{A : Set i}{B : A → Set j}
                 → {a a' : A}{b : B a}{b' : B a'}
                 → (Σ (a ≡ a') λ q → b ≡ subst B (sym q) b')
                 → (a , b) ≡ (a' , b')
          unapΣ' (refl , refl) = refl

      private
        module limit where
          module _ (i : I) where
            open Limit (X i) (π i) public

          isom : Cone ≅ (Z →ⁱ L)
          isom = Limit-univⁱ.univ-iso I Xⁱ πⁱ


      open limit public using (isom)
