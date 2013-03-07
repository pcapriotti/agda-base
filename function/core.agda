{-# OPTIONS --without-K #-}
module function.core where

open import level

-- copied from Agda's standard library

infixr 9 _∘'_
infixr 0 _$_

_∘'_ : ∀ {a b c}
      {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘' g = λ x → f (g x)

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

record Composition u₁ u₂ u₃ u₁₂ u₂₃ u₁₃
        : Set (lsuc (u₁ ⊔ u₂ ⊔ u₃ ⊔ u₁₂ ⊔ u₂₃ ⊔ u₁₃)) where
  infixl 9 _∘_
  field
    U₁ : Set u₁
    U₂ : Set u₂
    U₃ : Set u₃

    hom₁₂ : U₁ → U₂ → Set u₁₂
    hom₂₃ : U₂ → U₃ → Set u₂₃
    hom₁₃ : U₁ → U₃ → Set u₁₃

    _∘_ : {X₁ : U₁}{X₂ : U₂}{X₃ : U₃} → hom₂₃ X₂ X₃ → hom₁₂ X₁ X₂ → hom₁₃ X₁ X₃

func-comp : ∀ {i j k} → Composition _ _ _ _ _ _
func-comp {i}{j}{k} = record
  { U₁ = Set i
  ; U₂ = Set j
  ; U₃ = Set k
  ; hom₁₂ = λ X Y → X → Y
  ; hom₂₃ = λ X Y → X → Y
  ; hom₁₃ = λ X Y → X → Y
  ; _∘_ = λ f g x → f (g x) }

module ComposeInterface {u₁ u₂ u₃ u₁₂ u₂₃ u₁₃}
                        ⦃ comp : Composition u₁ u₂ u₃ u₁₂ u₂₃ u₁₃ ⦄ where
  open Composition comp public using (_∘_)
open ComposeInterface public
