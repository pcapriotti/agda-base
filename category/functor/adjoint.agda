{-# OPTIONS --without-K #-}

open import level
open import equality.core
open import function.isomorphism using (_≅_)
  renaming ( apply to apply≅
           ; invert to invert≅ )
open import category.category
open import category.functor
  using (Functor; module Functor)

module category.functor.adjoint {i}{j}{i'}{j'}
  (C : Category i j)(D : Category i' j')
  (F : Functor C D)(G : Functor D C) where

open Category
open Functor

record _⊣_ : Set (i ⊔ i' ⊔ j ⊔ j') where
  field
    adj : ∀ X Y → hom D (apply F X) Y ≅ hom C X (apply G Y)

  open Category C using ()
    renaming (_∘_ to _⋆_)
  open Category D using ()
    renaming (_∘_ to _✦_)

  Φ : ∀ {X}{Y} → hom D (apply F X) Y → hom C X (apply G Y)
  Φ {X}{Y} = apply≅ (adj X Y)

  Ψ : ∀ {X}{Y} → hom C X (apply G Y) → hom D (apply F X) Y
  Ψ {X}{Y} = invert≅ (adj X Y)

  field
    adj-nat : {X X' : obj C}{Y Y' : obj D}
              (f : hom C X' X)(g : hom D Y Y')
            → (k : hom D (apply F X) Y)
            → Φ (g ✦ k ✦ map F f)
            ≡ map G g ⋆ Φ k ⋆ f
