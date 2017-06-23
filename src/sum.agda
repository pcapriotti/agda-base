{-# OPTIONS --without-K  #-}
module sum where

open import level using (Level; _⊔_)
open import function.core

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : {l k : Level} (A : Set l) (B : Set k) → Set (l ⊔ k)
A × B = Σ A λ _ → B

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → (B x) → Set c}
        → ((x : A) → (y : B x) → C x y) → ((xy : Σ A B) → C (proj₁ xy) (proj₂ xy))
uncurry f (a , b) = f a b

uncurry' : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
        → (X → Y → Z)
        → (X × Y) → Z
uncurry' f (x , y) = f x y

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,⊎_] : ∀ {i i' j}{A : Set i}{A' : Set i'}{B : Set j}
      → (A → B) → (A' → B)
      → A ⊎ A' → B
[ f ,⊎ f' ] (inj₁ a) = f a
[ f ,⊎ f' ] (inj₂ a') = f' a'

map-⊎ : ∀ {i i' j j'}{A : Set i}{A' : Set i'}
      → {B : Set j}{B' : Set j'}
      → (A → B) → (A' → B')
      → A ⊎ A' → B ⊎ B'
map-⊎ g g' = [ inj₁ ∘' g ,⊎ inj₂ ∘' g' ]
