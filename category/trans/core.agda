{-# OPTIONS --without-K --type-in-type #-}

open import level using (_⊔_)
open import sum
open import function.core
open import function.overloading
open import category.graph.core
open import category.graph.morphism.core
open import category.category.core
open import category.functor.core
open import equality.core
open import equality.calculus using (_⊚_; _⁻¹)
open import equality.reasoning

module category.trans.core {C D : Category} where

open as-category C
open as-category D

Trans : Functor C D → Functor C D → Set
Trans F G = (X : obj C) → hom (apply F X) (apply G X)

nat-equation : (F G : Functor C D)(α : Trans F G) → total C → Set
nat-equation F G α ((X , Y), f) =
  α Y ∘ map F f ≡ map G f ∘ α X

natural : (F G : Functor C D) → Trans F G → Set
natural F G α = ∀ {X Y} (f : hom X Y) → nat-equation F G α ((X , Y) , f)

record Nat (F G : Functor C D) : Set where
  constructor nt
  field
    α : Trans F G
    α-nat : natural F G α

_⇒_ : Functor C D → Functor C D → Set
_⇒_ = Nat
infixr 1 _⇒_
