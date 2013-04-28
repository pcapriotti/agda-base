open import category.category.core
open import category.functor.core
open import category.functor.adjoint.core

module category.functor.adjoint.unit
  {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'}
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
open import category.trans.core

open as-category C
open as-category D
open _⊣_ adjunction

-- unit of the adjunction
adj-η : id ⇒ G ∘ F
adj-η = nt eta eta-natural
  where
    eta : ∀ X → hom X (apply G (apply F X))
    eta X = Φ id

    lem : {X X' : obj C}(f : hom X X')
        → id ∘ id ∘ map F f
        ≡ map F f ∘ id ∘ map F (id)
    lem f = cong (λ z → z ∘ map F f) (left-id _)
          ⊚ left-id _
          ⊚ sym (right-id _)
          ⊚ sym (right-id _)
          ⊚ cong (λ z → map F f ∘ id ∘ z)
                  (sym (map-id F _))

    eta-natural : natural id (G ∘ F) eta
    eta-natural {X} {Y} f = begin
        eta Y ∘ f
      ≡⟨ cong (λ z → z ∘ f) (sym (left-id _))
        ⊚ cong (λ z → z ∘ eta Y ∘ f) (sym (map-id G _)) ⟩
        map G (id) ∘ eta Y ∘ f
      ≡⟨ sym (adj-nat f (id) (id)) ⟩
        Φ (id ∘ id ∘ map F f)
      ≡⟨ cong Φ (lem f) ⟩
        Φ (map F f ∘ id ∘ map F id)
      ≡⟨ adj-nat (id) (map F f) (id)  ⟩
        map G (map F f) ∘ eta X ∘ id
      ≡⟨ right-id _ ⟩
        map G (map F f) ∘ eta X
      ∎
      where open ≡-Reasoning
