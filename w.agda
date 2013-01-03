{-# OPTIONS --without-K #-}
module w where

open import level
open import sum
open import equality.core
open import equality.calculus
open import equality.isomorphisms
open import function.extensionality
open import function.isomorphism
open import function.isomorphism.properties
open import sets.nat using (suc)
open import hott.hlevel
open import hott.univalence.properties

module Definition {li la lb}
                  (I : Set li)
                  (A : I → Set la)
                  (B : (i : I) → A i → Set lb) 
                  (r : (i : I)(a : A i)(b : B i a) → I) where
  data W (i : I) : Set (la ⊔ lb) where
    sup : (a : A i) → ((b : B i a) → W (r i a b)) → W i

module Properties {li la lb}
                  {I : Set li}
                  {A : I → Set la}
                  {B : (i : I) → A i → Set lb}
                  {r : (i : I)(a : A i)(b : B i a) → I} where
  open Definition I A B r

  W' : I → Set _
  W' i = Σ (A i) λ a → ((b : B i a) → W (r i a b))

  w-unfold : (i : I) → W i ≅ W' i
  w-unfold _ = iso f g H K
    where
      f : {i : I} → W i → W' i
      f (sup a f) = a , f

      g : {i : I} → W' i → W i
      g (a , f) = sup a f

      H : {i : I}(w : W i) → g (f w) ≡ w
      H (sup a f) = refl

      K : {i : I}(w : W' i) → f (g w) ≡ w
      K (a , f) = refl

  w-hlevel : ∀ {n} → ((i : I) → h (suc n) (A i)) → (i : I) → h (suc n) (W i)
  w-hlevel hA i (sup a f) (sup a' f') = iso-hlevel (sym≅ lem-iso)
    (Σ-hlevel (hA i a a') (λ p → Π-hlevel λ b → w-hlevel hA _ _ _))
    where
      open ≅-Reasoning

      transport : ∀ {l la lb}{X : Set l}
                  {A : Set la}{B : A → Set lb}
                → {a a' : A}(p : a ≡ a')
                → (k : (a : A) → B a → X)
                → (b : B a)
                → k a' (subst B p b) ≡ k a b
      transport refl k b = refl

      lem-transport : {a a' : A i}
                      (f : (b : B i a) → W (r i a b))
                      (f' : (b : B i a') → W (r i a' b))
                      (p : a ≡ a')
                    → (subst (λ a → (b : B i a) → W (r i a b)) p f ≡ f')
                    ≅ ((b : B i a) → f b ≡ subst W (transport p (r i) b) (f' (subst (B i) p b)))
      lem-transport f f' refl = sym≅ strong-ext-iso

      lem-iso : (sup a f ≡ sup a' f')
              ≅ Σ (a ≡ a') λ p → ∀ b → f b ≡ subst W (transport p (r i) b) (f' (subst (B i) p b))
      lem-iso = begin
          (sup a f ≡ sup a' f')
        ≅⟨ iso≡ (w-unfold i) ⟩
          (apply (w-unfold i) (sup a f) ≡ apply (w-unfold i) (sup a' f'))
        ≅⟨ sym≅ Σ-split-iso ⟩
          (Σ (a ≡ a') λ p → subst (λ a → (b : B i a) → W (r i a b)) p f ≡ f')
        ≅⟨ Σ-cong-iso refl≅ (lem-transport f f') ⟩
          (Σ (a ≡ a') λ p → ∀ b → f b ≡ subst W (transport p (r i) b) (f' (subst (B i) p b)))
        ∎
open Definition public
open Properties public using (w-hlevel)
