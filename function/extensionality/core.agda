{-# OPTIONS --without-K #-}
module function.extensionality.core where

open import level using (lsuc; _⊔_)
open import equality.core

Extensionality : ∀ i j → Set (lsuc (i ⊔ j))
Extensionality i j = {X : Set i}{Y : Set j}
                   → {f g : X → Y}
                   → ((x : X) → f x ≡ g x)
                   → f ≡ g

Extensionality' : ∀ i j → Set (lsuc (i ⊔ j))
Extensionality' i j = {X : Set i}{Y : X → Set j}
                    → {f g : (x : X) → Y x}
                    → ((x : X) → f x ≡ g x)
                    → f ≡ g

StrongExt : ∀ i j → Set (lsuc (i ⊔ j))
StrongExt i j = {X : Set i}{Y : X → Set j}
              → {f g : (x : X) → Y x}
              → (∀ x → f x ≡ g x) ≡ (f ≡ g)

funext-inv : ∀ {i j}{X : Set i}{Y : X → Set j}
        → {f g : (x : X) → Y x}
        → f ≡ g
        → (x : X) → f x ≡ g x
funext-inv refl x = refl
