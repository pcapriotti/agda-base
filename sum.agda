{-# OPTIONS --without-K  #-}
module sum where

open import function.core

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : (A : Set) (B : Set) → Set
A × B = Σ A λ _ → B

uncurry : {A : Set} {B : A → Set} {C : (x : A) → (B x) → Set}
        → ((x : A) → (y : B x) → C x y) → ((xy : Σ A B) → C (proj₁ xy) (proj₂ xy))
uncurry f (a , b) = f a b

uncurry' : {X : Set}{Y : Set}{Z : Set}
        → (X → Y → Z)
        → (X × Y) → Z
uncurry' f (x , y) = f x y

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,⊎_] : {A : Set}{A' : Set}{B : Set}
      → (A → B) → (A' → B)
      → A ⊎ A' → B
[ f ,⊎ f' ] (inj₁ a) = f a
[ f ,⊎ f' ] (inj₂ a') = f' a'

map-⊎ : {A : Set}{A' : Set}
      → {B : Set}{B' : Set}
      → (A → B) → (A' → B')
      → A ⊎ A' → B ⊎ B'
map-⊎ g g' = [ inj₁ ∘' g ,⊎ inj₂ ∘' g' ]
