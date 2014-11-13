{-# OPTIONS --without-K #-}

module container.core where

open import level
open import sum
open import function.core

record Container (li la lb : Level) : Set (lsuc (li ⊔ la ⊔ lb)) where
  constructor container
  field
    I : Set li
    A : I → Set la
    B : {i : I} → A i → Set lb
    r : {i : I}{a : A i} → B a → I

  -- functor associated to this indexed container
  F : ∀ {lx} → (I → Set lx) → I → Set _
  F X i = Σ (A i) λ a → (b : B a) → X (r b)

  -- homsets in the slice category
  _→ⁱ_ : ∀ {lx ly} → (I → Set lx) → (I → Set ly) → Set _
  X →ⁱ Y = (i : I) → X i → Y i

  -- identity of the slice category
  idⁱ : ∀ {lx}{X : I → Set lx} → X →ⁱ X
  idⁱ i x = x

  -- composition in the slice category
  _∘ⁱ_ : ∀ {lx ly lz} {X : I → Set lx}{Y : I → Set ly}{Z : I → Set lz}
       → (Y →ⁱ Z) → (X →ⁱ Y) → (X →ⁱ Z)
  (f ∘ⁱ g) i = f i ∘ g i

  -- morphism map for the functor F
  imap : ∀ {lx ly}
       → {X : I → Set lx}
       → {Y : I → Set ly}
       → (X →ⁱ Y)
       → (F X →ⁱ F Y)
  imap g i (a , f) = a , λ b → g (r b) (f b)
