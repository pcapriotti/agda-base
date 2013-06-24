{-# OPTIONS --without-K --type-in-type #-}

open import category.category.core
open import category.functor.core
open import category.functor.adjoint.core

module category.functor.adjoint.counit
  {C D : Category}
  (F : Functor C D)(G : Functor D C)
  (adjunction : F ⊣ G) where

open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.isomorphism
open import function.overloading
open import category.graph.core
open import category.graph.morphism.core
open import category.functor.ops
open import category.functor.adjoint.properties
open import category.trans.core

open as-category C
open as-category D
open _⊣_ adjunction

adj-ε : F ∘ G ⇒ id
adj-ε = nt eps eps-natural
  where
    eps : ∀ Y → hom (apply F (apply G Y)) Y
    eps Y = Ψ id

    lem : {Y Y' : obj D}(f : hom Y Y')
        → map G (id) ∘ id ∘ map G f
        ≡ map G f ∘ id ∘ id
    lem f = cong (λ z → z ∘ id ∘ map G f) (map-id G _)
          ⊚ cong (λ z → z ∘ map G f) (left-id _)
          ⊚ left-id _
          ⊚ sym (right-id _)
          ⊚ sym (right-id _)

    eps-natural : natural (F ∘ G) id eps
    eps-natural {Y} {Y'} f = begin
        eps Y' ∘ map F (map G f)
      ≡⟨ sym (cong (λ z → z ∘ map F (map G f))
                    (left-id _)) ⟩
        id ∘ eps Y' ∘ map F (map G f)
      ≡⟨ sym (adj-nat-op adjunction (map G f) id id) ⟩
        Ψ (map G (id) ∘ id ∘ map G f)
      ≡⟨ cong Ψ (lem f) ⟩
        Ψ (map G f ∘ id ∘ id)
      ≡⟨ adj-nat-op adjunction id f id ⟩
        f ∘ eps Y ∘ map F (id)
      ≡⟨ cong (λ z → f ∘ eps Y ∘ z) (map-id F _)
        ⊚ right-id _ ⟩
        f ∘ eps Y
      ∎
      where open ≡-Reasoning
