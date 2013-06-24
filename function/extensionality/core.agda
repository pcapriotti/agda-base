{-# OPTIONS --without-K --type-in-type #-}
module function.extensionality.core where

open import level using (lsuc; _⊔_)
open import equality.core

Extensionality : Set
Extensionality = {X Y : Set}
               → {f g : X → Y}
               → ((x : X) → f x ≡ g x)
               → f ≡ g

Extensionality' : Set
Extensionality' = {X : Set}{Y : X → Set}
                → {f g : (x : X) → Y x}
                → ((x : X) → f x ≡ g x)
                → f ≡ g

StrongExt : Set
StrongExt = {X : Set}{Y : X → Set}
          → {f g : (x : X) → Y x}
          → (∀ x → f x ≡ g x) ≡ (f ≡ g)

ext-inv : {X : Set}{Y : X → Set}
        → {f g : (x : X) → Y x}
        → f ≡ g
        → (x : X) → f x ≡ g x
ext-inv refl x = refl
