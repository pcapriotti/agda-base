{-# OPTIONS --without-K #-}

module container.core where

open import level
open import sum
open import equality
open import function

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

  -- extensionality
  funext-isoⁱ : ∀ {lx ly} {X : I → Set lx}{Y : I → Set ly}
              → {f g : X →ⁱ Y}
              → (∀ i x → f i x ≡ g i x)
              ≅ (f ≡ g)
  funext-isoⁱ {f = f}{g = g}
    = (Π-ap-iso refl≅ λ i → strong-funext-iso)
    ·≅ strong-funext-iso

  funext-invⁱ : ∀ {lx ly} {X : I → Set lx}{Y : I → Set ly}
              → {f g : X →ⁱ Y}
              → f ≡ g → ∀ i x → f i x ≡ g i x
  funext-invⁱ = invert funext-isoⁱ

  funextⁱ : ∀ {lx ly} {X : I → Set lx}{Y : I → Set ly}
          → {f g : X →ⁱ Y}
          → (∀ i x → f i x ≡ g i x) → f ≡ g
  funextⁱ = apply funext-isoⁱ

  -- morphism map for the functor F
  imap : ∀ {lx ly}
       → {X : I → Set lx}
       → {Y : I → Set ly}
       → (X →ⁱ Y)
       → (F X →ⁱ F Y)
  imap g i (a , f) = a , λ b → g (r b) (f b)

  -- action of a functor on homotopies
  hmap : ∀ {lx ly}
       → {X : I → Set lx}
       → {Y : I → Set ly}
       → {f g : X →ⁱ Y}
       → (∀ i x → f i x ≡ g i x)
       → (∀ i x → imap f i x ≡ imap g i x)
  hmap p i (a , u) = ap (_,_ a) (funext (λ b → p (r b) (u b)))

  hmap-id : ∀ {lx ly}
          → {X : I → Set lx}
          → {Y : I → Set ly}
          → (f : X →ⁱ Y)
          → ∀ i x
          → hmap (λ i x → refl {x = f i x}) i x ≡ refl
  hmap-id f i (a , u) = ap (ap (_,_ a)) (funext-id _)
