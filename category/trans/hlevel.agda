{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import equality.calculus
open import category.category
open import category.functor.core
open import category.trans.core
open import hott.hlevel
open import function.extensionality
open import function.isomorphism using (_≅_; iso)
open import function.isomorphism.properties
open import hott.hlevel

module category.trans.hlevel {i}{j}{i'}{j'}
  {C : Category i j}{D : Category i' j'} where

open Category C using (is-cat)
open Category D using (is-cat)

private
  module NatΣ (F G : Functor C D) where
    Nat' : Set _
    Nat' = Σ (Trans F G) (natural F G)

    unnat-Σ : Nat' → Nat F G
    unnat-Σ (α , nat) = nt α nat

    nat-Σ : Nat F G → Nat'
    nat-Σ (nt α nat) = α , nat

    nat-Σ-iso : Nat' ≅ Nat F G
    nat-Σ-iso = iso unnat-Σ nat-Σ (λ x → refl) (λ x → refl)

trans-hset : (F G : Functor C D) → h 2 (Trans F G)
trans-hset F G = Π-hlevel (λ X → trunc D _ _) 

natural-prop : (F G : Functor C D)
             → (α : Trans F G)
             → h 1 (natural F G α)
natural-prop F G α = iso-hlevel (lem (nat-equation F G α))
  (Π-hlevel (λ m → trunc D _ _ _ _))
  where
    lem : ∀ {i}(P : mor C → Set i)
        → ((m : mor C) → P m) ≅ (∀ {X Y} (f : hom X Y) → P ((X , Y) , f))
    lem P = iso (λ n f → n (_ , f))
                (λ n m → n (proj₂ m))
                (λ _ → refl) (λ _ → refl)

nat-hset : (F G : Functor C D) → h 2 (Nat F G)
nat-hset F G = iso-hlevel nat-Σ-iso
  (Σ-hlevel (trans-hset F G)
            (λ α → h↑ (natural-prop F G α)))
  where
    open NatΣ F G

nat-equality : {F G : Functor C D}
             → {n₁ n₂ : Nat F G}
             → (Nat.α n₁ ≡ Nat.α n₂)
             → n₁ ≡ n₂
nat-equality {F}{G} {nt α _} {nt β _} p = cong unnat-Σ (uncongΣ (p , p'))
  where
    p' = h1⇒prop (natural-prop F G β) _ _
    open NatΣ F G
