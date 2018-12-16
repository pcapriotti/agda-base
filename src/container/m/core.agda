module container.m.core where

open import level
open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.extensionality
open import container.core
open import container.equality
open import container.fixpoint

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

module Definition {li la lb}(c : Container li la lb) where
  open Container c public

  -- definition of indexed M-types using native Agda coinduction
  data M (i : I) : Set (la ⊔ lb) where
    inf : (a : A i) → ((b : B a) → ∞ (M (r b))) → M i

  -- the terminal coalgebra
  out : M →ⁱ F M
  out i (inf a f) = a , ♭ ∘' f

  -- normally, the constructor can be defined in terms of out and unfold, but
  -- Agda provides it natively, together with a definitional β rule
  inM' : F M →ⁱ M
  inM' i (a , f) = inf a (λ x → ♯ (f x))

  inM'-β : {i : I}(x : F M i) → out i (inM' i x) ≡ x
  inM'-β x = refl

  module Elim {lx}{X : I → Set lx}
              (α : X →ⁱ F X) where
    -- anamorphisms
    unfold : X →ⁱ M
    unfold i x = inf a f
      where
        u : F X i
        u = α i x

        a : A i
        a = proj₁ u

        f : (b : B a) → ∞ (M (r b))
        f b = ♯ unfold (r b) (proj₂ u b)

    -- computational rule for anamorphisms
    -- this holds definitionally
    unfold-β : {i : I}(x : X i)
             → out i (unfold i x) ≡ imap unfold i (α i x)
    unfold-β x = refl

    -- the corresponding η rule doesn't hold, so we postulate it
    postulate
      unfold-η : (h : X →ⁱ M)
               → (∀ {i} (x : X i) → out i (h i x) ≡ imap h i (α i x))
               → ∀ {i} (x : X i) → h i x ≡ unfold i x
  open Elim public

  -- using η, we can prove that the unfolding of out is the identity
  unfold-id : ∀ {i} (x : M i) → unfold out i x ≡ x
  unfold-id x = sym (unfold-η out idⁱ (λ _ → refl) x)

  -- the usual definition of the constructor
  inM : F M →ⁱ M
  inM = unfold (imap out)

  -- the constructor is the inverse of the destructor
  inM-η : ∀ {i} (x : M i) → inM i (out i x) ≡ x
  inM-η x = unfold-η out (inM ∘ⁱ out) (λ _ → refl) x · unfold-id x

  inM-β : ∀ {i} (x : F M i) → out i (inM i x) ≡ x
  inM-β {i} x = ap u (funext (λ i → funext inM-η))
    where
      u : (M →ⁱ M) → F M i
      u h = imap h i x

  fixpoint : ∀ i → M i ≅ F M i
  fixpoint i = iso (out i) (inM i) inM-η inM-β

  -- now we can prove that the constructor provided by Agda is equal to the
  -- usual one
  inM-alt : ∀ {i} (x : F M i) → inM' i x ≡ inM i x
  inM-alt {i} x = sym (inM-η (inM' i x))
