{-# OPTIONS --without-K #-}
module sets.nat.ordering.leq.hlevel where

open import sum
open import equality
open import function.isomorphism
open import function.extensionality
open import hott.hlevel
open import sets.nat.core
open import sets.nat.ordering.leq.core
open import container.core
open import container.w
open import sets.empty
open import sets.unit

open import hott.hlevel.sets public
  using (nat-set)

module ≤-container where
  I : Set
  I = ℕ × ℕ

  A A₁ A₂ : I → Set
  A₁ (m , n) = m ≡ 0
  A₂ (m , n) = ( Σ I λ { (m' , n')
               → m ≡ suc m'
               × n ≡ suc n' } )
  A i = A₁ i ⊎ A₂ i

  A₂-struct-iso : ∀ m n
                → A₂ (m , n)
                ≅ (¬ (m ≡ 0) × ¬ (n ≡ 0))
  A₂-struct-iso m n = iso f g α β
    where
      f : ∀ {m n} → A₂ (m , n) → ¬ (m ≡ 0) × ¬ (n ≡ 0)
      f .{suc m}.{suc n}((m , n) , refl , refl) = (λ ()) , (λ ())

      g : ∀ {m n} → ¬ (m ≡ 0) × ¬ (n ≡ 0) → A₂ (m , n)
      g {m = zero} (u , v) = ⊥-elim (u refl)
      g {n = zero} (u , v) = ⊥-elim (v refl)
      g {suc m} {suc n} _ = ((m , n) , refl , refl)

      α : ∀ {m n}(a : A₂ (m , n)) → g (f a) ≡ a
      α .{suc m}.{suc n}((m , n) , refl , refl) = refl

      β : ∀ {m n}(u : ¬ (m ≡ 0) × ¬ (n ≡ 0)) → f (g u) ≡ u
      β {m = zero} (u , v) = ⊥-elim (u refl)
      β {n = zero} (u , v) = ⊥-elim (v refl)
      β {suc m} {suc n} _ = pair≡ (funext λ ()) (funext λ ())

  A₂-h1 : ∀ i → h 1 (A₂ i)
  A₂-h1 (m , n) = iso-hlevel (sym≅ (A₂-struct-iso m n))
    (×-hlevel (Π-hlevel λ _ → ⊥-prop) (Π-hlevel λ _ → ⊥-prop))

  A-disj : ∀ i → ¬ (A₁ i × A₂ i)
  A-disj (.zero , n) (refl , (m' , n') , () , pn)

  A-h1 : ∀ i → h 1 (A i)
  A-h1 i = ⊎-h1 (nat-set _ zero) (A₂-h1 i) (A-disj i)

  B : ∀ {i} → A i → Set
  B (inj₁ _) = ⊥
  B (inj₂ _) = ⊤

  r : ∀ {i}{a : A i} → B a → I
  r {a = inj₁ _} ()
  r {a = inj₂ (mn' , _)} _ = mn'

  c : Container
  c = container I A B r

open ≤-container using (c; A-h1)

≤-struct-iso : ∀ {n m}
             → n ≤ m
             ≅ W c (n , m)
≤-struct-iso = iso f g α β
  where
    f : ∀ {n m} → n ≤ m → W c (n , m)
    f z≤n = sup (inj₁ refl) (λ ())
    f (s≤s p) = sup (inj₂ (_ , (refl , refl))) (λ _ → f p)

    g : ∀ {m n} → W c (m , n) → m ≤ n
    g (sup (inj₁ refl) _) = z≤n
    g (sup (inj₂ ((m' , n') , (refl , refl))) u)
      = s≤s (g (u tt))

    α : ∀ {n m}(p : n ≤ m) → g (f p) ≡ p
    α z≤n = refl
    α (s≤s p) = ap s≤s (α p)

    β : ∀ {n m}(p : W c (m , n)) → f (g p) ≡ p
    β (sup (inj₁ refl) u) = ap (sup (inj₁ refl)) (funext λ ())
    β (sup (inj₂ ((m' , n') , (refl , refl))) u)
      = ap (sup _) (funext λ { tt → β (u tt) })

≤-hlevel : ∀ {m n} → h 1 (m ≤ n)
≤-hlevel {m}{n} = iso-hlevel (sym≅ ≤-struct-iso) (w-hlevel A-h1 (m , n))
