{-# OPTIONS --without-K --type-in-type #-}

open import category.category.core
open import category.functor.core

module category.functor.adjoint.core where

open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.isomorphism.core
open import function.overloading
open import category.graph.core
open import category.graph.morphism.core

record _⊣_ {C D : Category}
           (F : Functor C D)(G : Functor D C)
         : Set where
  open as-category C
  open as-category D

  field
    adj : ∀ X Y → hom (apply F X) Y ≅ hom X (apply G Y)

  Φ : ∀ {X}{Y} → hom (apply F X) Y → hom X (apply G Y)
  Φ {X}{Y} = apply (adj X Y)

  Ψ : ∀ {X}{Y} → hom X (apply G Y) → hom (apply F X) Y
  Ψ {X}{Y} = invert (adj X Y)

  field
    adj-nat : {X X' : obj C}{Y Y' : obj D}
              (f : hom X' X)(g : hom Y Y')
            → (k : hom (apply F X) Y)
            → Φ (g ∘ k ∘ map F f)
            ≡ map G g ∘ Φ k ∘ f
