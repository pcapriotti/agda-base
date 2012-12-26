{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import category.category
open import category.functor
open import category.trans.core
open import hott.hlevel
open import function.extensionality
open import function.isomorphism using (_≅_; iso)
open import function.isomorphism.properties
open import hott.hlevel
open import hott.univalence.properties

module category.trans.hlevel {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

open Category using (mor; hom)

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