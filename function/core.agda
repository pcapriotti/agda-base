{-# OPTIONS --without-K --type-in-type #-}
module function.core where

-- copied from Agda's standard library

infixr 9 _∘'_
infixr 0 _$_

_∘'_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘' g = λ x → f (g x)

const : {A : Set} {B : Set} → A → B → A
const x = λ _ → x

_$_ : {A : Set} {B : A → Set} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

flip : {A : Set} {B : Set} {C : A → B → Set} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

record Composition : Set where
  infixl 9 _∘_
  field
    U₁ : Set
    U₂ : Set
    U₃ : Set

    hom₁₂ : U₁ → U₂ → Set
    hom₂₃ : U₂ → U₃ → Set
    hom₁₃ : U₁ → U₃ → Set

    _∘_ : {X₁ : U₁}{X₂ : U₂}{X₃ : U₃} → hom₂₃ X₂ X₃ → hom₁₂ X₁ X₂ → hom₁₃ X₁ X₃

record Identity : Set where
  field
    U : Set
    endo : U → Set
    id : {X : U} → endo X

func-comp : Composition
func-comp = record
  { U₁ = Set
  ; U₂ = Set
  ; U₃ = Set
  ; hom₁₂ = λ X Y → X → Y
  ; hom₂₃ = λ X Y → X → Y
  ; hom₁₃ = λ X Y → X → Y
  ; _∘_ = λ f g x → f (g x) }

func-id : Identity
func-id = record
  { U = Set
  ; endo = λ X → X → X
  ; id = λ x → x }

module ComposeInterface ⦃ comp : Composition ⦄ where
  open Composition comp public using (_∘_)
open ComposeInterface public

module IdentityInterface ⦃ identity : Identity ⦄ where
  open Identity identity public using (id)
open IdentityInterface public
