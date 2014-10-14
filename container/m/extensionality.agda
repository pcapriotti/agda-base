{-# OPTIONS --without-K #-}
module container.m.extensionality where

open import sum
open import equality
open import container.core
open import container.fixpoint
open import container.equality
open import container.m.core

module Extensionality {li la lb}(c : Container li la lb) where
  private
    module C where
      open Definition c public

      fp : Fixpoint c _
      fp = fix M fixpoint

      open Fixpoint fp public
        using (head; tail)

    module S where
      open Equality c C.fp
        using (equality)
      open Definition equality public

      fp : Fixpoint equality _
      fp = fix M fixpoint

      open Fixpoint fp public
        using (head; tail)

    open C

  -- bisimilarity relation
  _≡M_ : ∀ {i}(u v : M i) → Set _
  u ≡M v = S.M (_ , u , v)

  Eq : S.I → Set _
  Eq (i , u , v) = u ≡ v

  mext-inv : ∀ {i}{u v : M i} → u ≡ v → u ≡M v
  mext-inv = S.unfold f
    where
      f : ∀ {i} {u v : M i} → Eq (i , u , v) → S.F Eq (i , u , v)
      f refl = refl , (λ { (i , ._ , ._) (b , refl , refl) → refl })

  reflM : ∀ {i}{u : M i} → u ≡M u
  reflM = mext-inv refl

  private
    -- total space of bisimilarity
    E : ∀ i → Set _
    E i = Σ (M i × M i) (uncurry _≡M_)

    f : E ↝ F E
    f ((xs , ys) , bisim)
      = head xs , λ i b
      → let b' = subst (λ a → B a i) (S.head bisim) b
      in (tail xs i b , tail ys i b') , S.tail bisim _ (b , refl , refl)

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
            → (f : ∀ j → B a' j → M j)
            → _≡_ {A = F M i}
              (a' , f)
              (a ,  λ j b → f j (subst (λ a → B a j) p b))
        lem refl f = refl

    equal-π : ∀ {i}(e : E i) → π₁ e ≡ π₂ e
    equal-π e = unfold-η f π₁ π₁-mor e · sym (unfold-η f π₂ π₂-mor e)

    abstract
      mext₀ : ∀ {i} {xs ys : M i} → xs ≡M ys → xs ≡ ys
      mext₀ p = equal-π (_ , p)

  mext : ∀ {i} {xs ys : M i} → xs ≡M ys → xs ≡ ys
  mext p = mext₀ p · sym (mext₀ reflM)

  mext-id : ∀ {i}{u : M i} → mext (reflM {u = u}) ≡ refl
  mext-id = left-inverse (mext₀ reflM)

  mext-retraction : ∀ {i}{xs ys : M i}(p : xs ≡ ys)
                  → mext (mext-inv p) ≡ p
  mext-retraction refl = left-inverse (mext₀ reflM)
