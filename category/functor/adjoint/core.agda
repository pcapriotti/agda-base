{-# OPTIONS --without-K #-}

open import category.category
open import category.functor.core

module category.functor.adjoint.core where

open import level
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.isomorphism
open import function.overloading
open import category.graph

record _⊣_ {i}{j}{i'}{j'}
           {C : Category i j}{D : Category i' j'}
           (F : Functor C D)(G : Functor D C)
         : Set (i ⊔ j ⊔ i' ⊔ j') where
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
