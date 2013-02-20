{-# OPTIONS --without-K #-}

module m where

open import level
open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.extensionality

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

-- non-indexed M types, A and B define a container
module Definition (A : Set)
                  (B : A → Set) where
  -- functor associated to this container
  F : Set → Set
  F X = Σ A λ a → (B a → X)

  -- morphism map for the functor F
  fmap : {X Y : Set}
       → (X → Y)
       → F X → F Y
  fmap g (a , f) = a , g ∘ f

  -- definition of M-types using native Agda coinduction
  data M : Set where
    inf : (a : A) → (B a → ∞ M) → M

  -- the terminal coalgebra
  out : M → F M
  out (inf a f) = a , ♭ ∘ f

  -- normally, the constructor can be defined in terms of out and unfold, but
  -- Agda provides it natively, together with a definitional β rule
  inM' : F M → M
  inM' (a , f) = inf a (λ x → ♯ (f x))

  inM'-β : (x : F M) → out (inM' x) ≡ x
  inM'-β x = refl

  module Elim {X : Set}
              (α : X → F X) where
    -- anamorphisms
    unfold : X → M
    unfold x = inf a f
      where
        u : F X
        u = α x

        a : A
        a = proj₁ u

        f : B a → ∞ M
        f b = ♯ unfold (proj₂ u b)

    -- computational rule for anamorphisms
    -- this holds definitionally
    unfold-β : (x : X) → out (unfold x) ≡ fmap unfold (α x)
    unfold-β x = refl

    -- the corresponding η rule doesn't hold, so we postulate it
    postulate
      unfold-η : (h : X → M)
               → ((x : X) → out (h x) ≡ fmap h (α x))
               → (x : X) → h x ≡ unfold x
  open Elim

  -- using η, we can prove that the unfolding of out is the identity
  unfold-id : (x : M) → unfold out x ≡ x
  unfold-id x = sym (unfold-η out id (λ _ → refl) x)

  -- the usual definition of the constructor
  inM : F M → M
  inM = unfold (fmap out)

  -- the constructor is the inverse of the destructor
  inM-η : (x : M) → inM (out x) ≡ x
  inM-η x = unfold-η out (inM ∘ out) (λ _ → refl) x ⊚ unfold-id x

  inM-β : (x : F M) → out (inM x) ≡ x
  inM-β x = cong (λ h → fmap h x) (ext' inM-η)

  -- now we can prove that the constructor provided by Agda is equal to the
  -- usual one
  inM-alt : (x : F M) → inM' x ≡ inM x
  inM-alt x = sym (inM-η (inM' x))
open Definition
