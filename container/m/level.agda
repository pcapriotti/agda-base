module container.m.level where

open import level
open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.extensionality
open import sets.unit
open import sets.nat.core
open import hott.level
open import hott.univalence
open import container.core
open import container.equality
open import container.fixpoint
open import container.m.core
open import container.m.extensionality

private
  module Properties {li la lb}
                    {c : Container li la lb}
                    (hA : ∀ i → contr (Container.A c i)) where
    open Definition c
    open Extensionality c
    open Fixpoint (fix M fixpoint)
      using (head; tail)

    module S where
      module local where
        open Equality c (fix M fixpoint)
          using (equality)
        open Definition equality public

      open Fixpoint (fix local.M local.fixpoint) public
        using (head; tail)
      open local public

    center : ∀ {i} → M i
    center {i} = inf (proj₁ (hA i)) λ _ _ → ♯ center

    Center : S.I → Set _
    Center (i , x , y) = center ≡ x

    contraction : ∀ {i} (x : M i) → center ≡ x
    contraction {i} x = mext (lem' x)
      where
        coalg : ∀ {i}{x y : M i} → center ≡ x → S.F Center (i , x , y)
        coalg {i}{y = y} refl
          = proj₂ (hA i) (head y)
          , λ { (j , ._ , ._) (b , refl , refl) → refl }

        lem' : ∀ {i}(x : M i) → center ≡M x
        lem' _ = S.unfold coalg refl

    m-contr : ∀ i → contr (M i)
    m-contr i = center , contraction

m-level : ∀ {n li la lb} {c : Container li la lb}
         → let open Definition c
         in ((i : I) → h n (A i))
         → (i : I) → h n (M i)
m-level {n = 0} hA i = Properties.m-contr hA i
m-level {n = suc n} {c = c} hA i = λ xs ys
  → retract-level mext mext-inv mext-retraction (ih xs ys)
  where
    open Definition c
    open Extensionality c
    open Fixpoint (fix M fixpoint)
      using (head; tail)

    ih : (xs ys : M i) → h n (xs ≡M ys)
    ih xs ys = m-level (λ { (i , xs , ys) → hA i (head xs) (head ys) })
                        (i , xs , ys)
