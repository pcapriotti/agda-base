{-# OPTIONS --without-K  #-}
module sum where

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
