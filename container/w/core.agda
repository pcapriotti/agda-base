module container.w.core where

open import level
open import sum
open import equality
open import function.extensionality
open import function.isomorphism
open import function.isomorphism.properties
open import function.overloading
open import sets.empty
open import sets.nat.core using (suc)
open import sets.unit
open import hott.level
open import container.core
open import container.fixpoint
open import container.equality

private
  module Definition {li la lb} (c : Container li la lb) where
    open Container c

    -- definition of indexed W-types using a type family
    data W (i : I) : Set (la ⊔ lb) where
      sup : (a : A i) → ((b : B a) → W (r b)) → W i

    -- initial F-algebra
    inW : F W →ⁱ W
    inW i (a , f) = sup a f

    module Elim {lx} {X : I → Set lx}
                (α : F X →ⁱ X) where
      -- catamorphisms
      fold : W →ⁱ X
      fold i (sup a f) = α i (a , λ b → fold _ (f b))

      -- computational rule for catamorphisms
      -- this holds definitionally
      fold-β : ∀ {i} (x : F W i) → fold i (inW i x) ≡ α i (imap fold i x)
      fold-β x = refl

      -- η-rule, this is only propositional
      fold-η : (h : W →ⁱ X)
             → (∀ {i} (x : F W i) → h i (inW i x) ≡ α i (imap h i x))
             → ∀ {i} (x : W i) → h i x ≡ fold i x
      fold-η h p {i} (sup a f) = p (a , λ b → f b) · lem
        where
          lem : α i (a , (λ b → h _ (f b)))
              ≡ α i (a , (λ b → fold _ (f b)))
          lem = ap (λ z → α i (a , z))
                     (funext λ b → fold-η h p (f b))
    open Elim public

    head : ∀ {i} → W i → A i
    head (sup a f) = a

    tail : ∀ {i} (x : W i)(b : B (head x)) → W (r b)
    tail (sup a f) = f

    fixpoint : (i : I) → W i ≅ F W i
    fixpoint _ = iso f g H K
      where
        f : {i : I} → W i → F W i
        f (sup a f) = a , f

        g : {i : I} → F W i → W i
        g (a , f) = sup a f

        H : {i : I}(w : W i) → g (f w) ≡ w
        H (sup a f) = refl

        K : {i : I}(w : F W i) → f (g w) ≡ w
        K (a , f) = refl

private
  module Properties {li la lb}{c : Container li la lb} where
    open Container c
    open Definition c

    open Equality c (fix W fixpoint)
    open Container equality
      using ()
      renaming (F to F-≡')
    open Definition equality
      using ()
      renaming ( W to W-≡
               ; fixpoint to fixpoint-≡ )

    F-≡ : ∀ {lx}
        → (∀ {i} → W i → W i → Set lx)
        → (∀ {i} → W i → W i → Set _)
    F-≡ X  u v = F-≡' (λ {(i , u , v) → X {i} u v}) (_ , u , v)

    _≡W_ : ∀ {i} → W i → W i → Set _
    _≡W_ {i} u v = W-≡ (i , u , v)

    fixpoint-W : ∀ {i}{u v : W i} → (u ≡ v) ≅ F-≡ _≡_ u v
    fixpoint-W {i}{sup a f}{sup a' f'} = begin
        (sup a f ≡ sup a' f')
      ≅⟨ iso≡ (fixpoint i) ⟩
        (apply (fixpoint i) (sup a f) ≡ apply (fixpoint i) (sup a' f'))
      ≅⟨ sym≅ Σ-split-iso ⟩
        (Σ (a ≡ a') λ p → subst (λ a → (b : B a) → W (r b)) p f ≡ f')
      ≅⟨ Σ-ap-iso refl≅ (substX-β f f') ⟩
        (Σ (a ≡ a') λ p → ∀ b → f b ≡ substX p b (f' (subst B p b)))
      ∎
      where open ≅-Reasoning

    str-iso : ∀ {i}{u v : W i} → (u ≡ v) ≅ (u ≡W v)
    str-iso {i}{sup a f}{sup a' f'} = begin
        (sup a f ≡ sup a' f')
      ≅⟨ fixpoint-W ⟩
        (Σ (a ≡ a') λ p → ∀ b → f b ≡ substX p b (f' (subst B p b)))
      ≅⟨ Σ-ap-iso refl≅ (λ a → Π-ap-iso refl≅ λ b → str-iso) ⟩
        (Σ (a ≡ a') λ p → ∀ b → f b ≡W substX p b (f' (subst B p b)))
      ≅⟨ sym≅ (fixpoint-≡ _) ⟩
        (sup a f ≡W sup a' f')
      ∎
      where open ≅-Reasoning

    w-level : ∀ {n} → ((i : I) → h (suc n) (A i)) → (i : I) → h (suc n) (W i)
    w-level hA i (sup a f) (sup a' f') = iso-level (sym≅ lem)
      (Σ-level (hA i a a') (λ p → Π-level λ b → w-level hA _ _ _))
      where
        lem : ∀ {i}{a a' : A i}
              {f : (b : B a) → W (r b)}
              {f' : (b : B a') → W (r b)}
            → (sup a f ≡ sup a' f')
            ≅ Σ (a ≡ a') λ p → ∀ b → f b ≡ substX p b (f' (subst B p b))
        lem = fixpoint-W

open Definition public
open Properties public using (w-level)
