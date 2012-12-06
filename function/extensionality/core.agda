{-# OPTIONS --without-K #-}
module function.extensionality.core where

open import level using (lsuc; _⊔_)
open import equality.core

Extensionality : ∀ i j → Set (lsuc (i ⊔ j))
Extensionality i j = {X : Set i}{Y : Set j}
                   → (f g : X → Y)
                   → ((x : X) → f x ≡ g x)
                   → f ≡ g

Extensionality' : ∀ i j → Set (lsuc (i ⊔ j))
Extensionality' i j = {X : Set i}{Y : X → Set j}
                    → (f g : (x : X) → Y x)
                    → ((x : X) → f x ≡ g x)
                    → f ≡ g