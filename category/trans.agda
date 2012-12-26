{-# OPTIONS --without-K #-}

open import level using (_⊔_)
open import sum
open import category.category
open import category.functor using
  (Functor; module Functor)
open import equality.core
open import equality.calculus using (_⊚_; _⁻¹)
open import equality.reasoning
open import function.extensionality
open import function.isomorphism using (_≅_; iso)
open import function.isomorphism.properties
open import hott.hlevel
open import hott.univalence.properties

module category.trans {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

open Category using (obj; hom; mor)
open Category D using (_∘_)
open Functor using (apply; map)

Trans : Functor C D → Functor C D → Set _
Trans F G = ∀ X → hom D (apply F X) (apply G X)

nat-equation : (F G : Functor C D)(α : Trans F G) → mor C → Set _
nat-equation F G α ((X , Y), f) =
  α Y ∘ map F f ≡ map G f ∘ α X

natural : (F G : Functor C D) → Trans F G → Set _
natural F G α = ∀ {X Y} (f : hom C X Y) → nat-equation F G α ((X , Y) , f)

Nat : Functor C D → Functor C D → Set _
Nat F G = Σ (Trans F G) (natural F G)

Id : (F : Functor C D) → Nat F F
Id F = (λ X → id (apply F X))
     , ( λ f → left-unit (map F f)
             ⊚ right-unit (map F f) ⁻¹ )
  where
    open Category D

Compose : {F G H : Functor C D} → Nat G H → Nat F G → Nat F H
Compose {F}{G}{H} (α , α-nat) (β , β-nat) = γ , γ-nat
  where
    open ≡-Reasoning
    open Category D using (associativity)

    γ : ∀ X → hom D (apply F X) (apply H X)
    γ X = α X ∘ β X

    γ-nat : ∀ {X Y} (f : hom C X Y)
          → γ Y ∘ map F f ≡ map H f ∘ γ X
    γ-nat {X}{Y} f = begin
        γ Y ∘ map F f
      ≡⟨ associativity _ _ _ ⟩
        α Y ∘ (β Y ∘ map F f)
      ≡⟨ cong (_∘_ (α Y)) (β-nat f) ⟩
        α Y ∘ (map G f ∘ β X)
      ≡⟨ sym (associativity _ _ _) ⟩
        α Y ∘ map G f ∘ β X
      ≡⟨ cong (λ z → z ∘ β X) (α-nat f) ⟩
        map H f ∘ α X ∘ β X
      ≡⟨ associativity _ _ _ ⟩
        map H f ∘ γ X
      ∎

trans-hset : (F G : Functor C D) → h 2 (Trans F G)
trans-hset F G = Π-hlevel strong-ext 2 (λ X → trunc _ _) 
  where open Category D

natural-prop : (F G : Functor C D)
             → (α : Trans F G)
             → h 1 (natural F G α)
natural-prop F G α = iso-h (lem (nat-equation F G α)) 1
  (Π-hlevel strong-ext 1 (λ m → trunc _ _ _ _))
  where
    open Category D using (trunc)

    lem : ∀ {i}(P : mor C → Set i)
        → ((m : mor C) → P m) ≅ (∀ {X Y} (f : hom C X Y) → P ((X , Y) , f))
    lem P = iso (λ n f → n (_ , f))
                (λ n m → n (proj₂ m))
                (λ _ → refl) (λ _ → refl)

nat-hset : (F G : Functor C D) → h 2 (Nat F G)
nat-hset F G = Σ-hlevel 2 (trans-hset F G)
                          (λ α → h↑ 1 (natural-prop F G α))

record NatEq (F G : Functor C D) : Set (i ⊔ j ⊔ j') where
  constructor nat-eq
  field
    nat-apply : Nat F G
    nat-invert : Nat G F

coerce₁ : {F G : Functor C D}
        → F ≡ G → NatEq F G
coerce₁ {F} {.F} refl = nat-eq (Id F) (Id F)
