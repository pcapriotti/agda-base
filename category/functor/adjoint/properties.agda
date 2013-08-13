open import category.category.core
open import category.functor.core
open import category.functor.adjoint.core

module category.functor.adjoint.properties
  {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'}
  {F : Functor C D}{G : Functor D C}
  (adjunction : F ⊣ G) where

open import equality.core
open import equality.reasoning
open import function.core
open import function.isomorphism
open import function.overloading
open import category.graph.core
open import category.graph.morphism.core

open as-category C
open as-category D
open _⊣_ adjunction

adj-nat-op : {X X' : obj C}{Y Y' : obj D}
           → (f : hom X' X)(g : hom Y Y')
           → (k : hom X (apply G Y))
           → Ψ (map G g ∘ k ∘ f)
           ≡ g ∘ Ψ k ∘ map F f
adj-nat-op {X}{X'}{Y}{Y'} f g k = begin
    Ψ (map G g ∘ k ∘ f)
  ≡⟨ ap (λ k → Ψ (map G g ∘ k ∘ f))
            (sym (_≅_.iso₂ (adj X Y) k)) ⟩
    Ψ (map G g ∘ Φ (Ψ k) ∘ f)
  ≡⟨ ap Ψ (sym (adj-nat f g (Ψ k))) ⟩
    Ψ (Φ (g ∘ Ψ k ∘ map F f))
  ≡⟨ _≅_.iso₁ (adj X' Y') _ ⟩
    g ∘ Ψ k ∘ map F f
  ∎
  where open ≡-Reasoning
