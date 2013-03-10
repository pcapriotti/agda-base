{-# OPTIONS --without-K #-}

open import level
open import equality.core
open import equality.calculus using (_⊚_)
open import equality.reasoning
open import function.isomorphism using (_≅_; module _≅_)
  renaming ( apply to apply≅
           ; invert to invert≅ )
open import category.structure
open import category.graph
  hiding (Compose; Id)
open import category.category
open import category.functor.core
open import category.trans.core
  using (_⇒_; nt; natural)

module category.functor.adjoint {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'}
  (F : Functor C D)(G : Functor D C) where

open Functor

record _⊣_ : Set (i ⊔ i' ⊔ j ⊔ j') where
  field
    adj : ∀ X Y → hom D (apply F X) Y ≅ hom C X (apply G Y)

  Φ : ∀ {X}{Y} → hom D (apply F X) Y → hom C X (apply G Y)
  Φ {X}{Y} = apply≅ (adj X Y)

  Ψ : ∀ {X}{Y} → hom C X (apply G Y) → hom D (apply F X) Y
  Ψ {X}{Y} = invert≅ (adj X Y)

  open cat-interface C
  open cat-interface D

  field
    adj-nat : {X X' : obj C}{Y Y' : obj D}
              (f : hom C X' X)(g : hom D Y Y')
            → (k : hom D (apply F X) Y)
            → Φ (g ∘ k ∘ map F f)
            ≡ map G g ∘ Φ k ∘ f

  open ≡-Reasoning

  adj-nat-op : {X X' : obj C}{Y Y' : obj D}
               (f : hom C X' X)(g : hom D Y Y')
             → (k : hom C X (apply G Y))
             → Ψ (map G g ∘ k ∘ f)
             ≡ g ∘ Ψ k ∘ map F f
  adj-nat-op {X}{X'}{Y}{Y'} f g k = begin
      Ψ (map G g ∘ k ∘ f)
    ≡⟨ cong (λ k → Ψ (map G g ∘ k ∘ f))
              (sym (_≅_.iso₂ (adj X Y) k)) ⟩
      Ψ (map G g ∘ Φ (Ψ k) ∘ f)
    ≡⟨ cong Ψ (sym (adj-nat f g (Ψ k))) ⟩
      Ψ (Φ (g ∘ Ψ k ∘ map F f))
    ≡⟨ _≅_.iso₁ (adj X' Y') _ ⟩
      g ∘ Ψ k ∘ map F f
    ∎

  -- unit of the adjunction
  η : Id C ⇒ G ∘ F
  η = nt eta eta-natural
    where
      eta : ∀ X → hom C X (apply G (apply F X))
      eta X = Φ id

      lem : {X X' : obj C}(f : hom C X X')
          → id ∘ id ∘ map F f
          ≡ map F f ∘ id ∘ map F (id)
      lem f = cong (λ z → z ∘ map F f) (left-unit _)
            ⊚ left-unit _
            ⊚ sym (right-unit _)
            ⊚ sym (right-unit _)
            ⊚ cong (λ z → map F f ∘ id ∘ z)
                    (sym (map-id F _))

      eta-natural : natural (Id C) (G ∘ F) eta
      eta-natural {X} {Y} f = begin
          eta Y ∘ f
        ≡⟨ cong (λ z → z ∘ f) (sym (left-unit _))
          ⊚ cong (λ z → z ∘ eta Y ∘ f) (sym (map-id G _)) ⟩
          map G (id) ∘ eta Y ∘ f
        ≡⟨ sym (adj-nat f (id) (id)) ⟩
          Φ (id ∘ id ∘ map F f)
        ≡⟨ cong Φ (lem f) ⟩
          Φ (map F f ∘ id ∘ map F id)
        ≡⟨ adj-nat (id) (map F f) (id)  ⟩
          map G (map F f) ∘ eta X ∘ id
        ≡⟨ right-unit _ ⟩
          map G (map F f) ∘ eta X
        ∎

  -- counit of the adjunction
  ε : F ∘ G ⇒ Id D
  ε = nt eps eps-natural
    where
      eps : ∀ Y → hom D (apply F (apply G Y)) Y
      eps Y = Ψ id

      lem : {Y Y' : obj D}(f : hom D Y Y')
          → map G (id) ∘ id ∘ map G f
          ≡ map G f ∘ id ∘ id
      lem f = cong (λ z → z ∘ id ∘ map G f) (map-id G _)
            ⊚ cong (λ z → z ∘ map G f) (left-unit _)
            ⊚ left-unit _
            ⊚ sym (right-unit _)
            ⊚ sym (right-unit _)

      eps-natural : natural (F ∘ G) (Id D) eps
      eps-natural {Y} {Y'} f = begin
          eps Y' ∘ map F (map G f)
        ≡⟨ sym (cong (λ z → z ∘ map F (map G f))
                      (left-unit _)) ⟩
          id ∘ eps Y' ∘ map F (map G f)
        ≡⟨ sym (adj-nat-op (map G f) (id) (id)) ⟩
          Ψ (map G (id) ∘ id ∘ map G f)
        ≡⟨ cong Ψ (lem f) ⟩
          Ψ (map G f ∘ id ∘ id)
        ≡⟨ adj-nat-op (id) f (id) ⟩
          f ∘ eps Y ∘ map F (id)
        ≡⟨ cong (λ z → f ∘ eps Y ∘ z) (map-id F _)
          ⊚ right-unit _ ⟩
          f ∘ eps Y
        ∎
