{-# OPTIONS --without-K --type-in-type #-}

module container.m.extensionality where

open import sum
open import equality
open import container.core
open import container.fixpoint
open import container.equality
open import container.m.core

module Extensionality (c : Container) where
  private
    module C where
      open Definition c public

      fp : Fixpoint c
      fp = fix M fixpoint

      open Fixpoint fp public
        using (head; tail)

    module S where
      open Equality c C.fp
        using (equality)
      open Equality c C.fp public
        using (substX)
      open Definition equality public

      fp : Fixpoint equality
      fp = fix M fixpoint

      open Fixpoint fp public
        using (head; tail)

    open C

  -- bisimilarity relation
  _≡M_ : ∀ {i}(u v : M i) → Set
  u ≡M v = S.M (_ , u , v)

  reflM : ∀ {i}{u : M i} → u ≡M u
  reflM = S.inf refl (λ b → ♯ reflM)

  private
    -- total space of bisimilarity
    E : ∀ i → Set
    E i = Σ (M i × M i) (uncurry _≡M_)

    f : E ↝ F E
    f ((xs , ys) , bisim)
      = head xs
      , (λ b → (( tail xs b
                , S.substX (S.head bisim) b
                           (tail ys (subst B (S.head bisim) b)))
                , S.tail bisim b))

    π₁ : E ↝ M
    π₁ ((xs , _), _) = xs

    π₁-mor : ∀ {i} (e : E i) → out (π₁ e) ≡ imap E π₁ (f e)
    π₁-mor ((xs , ys) , p) = refl

    π₂ : E ↝ M
    π₂ ((_ , ys), _) = ys

    π₂-mor : ∀ {i} (e : E i) → out (π₂ e) ≡ imap E π₂ (f e)
    π₂-mor {i} ((xs , ys) , bisim) = lem (S.head bisim) (tail ys)
      where
        lem : {a a' : A i}(p : a ≡ a')
            → (f : (b' : B a') → M (r b'))
            → _≡_ {A = F M i}
              (a' , f)
              (a , λ b → S.substX p b (f (subst B p b)))
        lem refl f = refl

    equal-π : ∀ {i}(e : E i) → π₁ e ≡ π₂ e
    equal-π e = unfold-η f π₁ π₁-mor e · sym (unfold-η f π₂ π₂-mor e)

    abstract
      mext₀ : ∀ {i} {xs ys : M i} → xs ≡M ys → xs ≡ ys
      mext₀ p = equal-π (_ , p)

  mext-inv : ∀ {i}{xs ys : M i} → xs ≡ ys → xs ≡M ys
  mext-inv refl = reflM

  mext : ∀ {i} {xs ys : M i} → xs ≡M ys → xs ≡ ys
  mext p = mext₀ p · sym (mext₀ reflM)

  mext-id : ∀ {i}{u : M i} → mext (reflM {u = u}) ≡ refl
  mext-id = left-inverse (mext₀ reflM)

  mext-retraction : ∀ {i}{xs ys : M i}(p : xs ≡ ys)
                  → mext (mext-inv p) ≡ p
  mext-retraction refl = left-inverse (mext₀ reflM)
