{-# OPTIONS --without-K --type-in-type #-}

module container.m.hlevel where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.extensionality
open import sets.unit
open import sets.nat
open import hott.hlevel
open import hott.univalence
open import container.core
open import container.equality
open import container.fixpoint
open import container.m.core
open import container.m.extensionality

private
  module Properties {c : Container}
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
    center {i} = inf (proj₁ (hA i)) λ _ → ♯ center

    contraction : ∀ {i} (x : M i) → center ≡ x
    contraction {i} x = mext (lem x)
      where
        lem : ∀ {i}(x : M i) → center ≡M x
        lem {i} x = S.inf (proj₂ (hA i) (head x))
                          (λ b → ♯ lem _)

    m-contr : ∀ i → contr (M i)
    m-contr i = center , contraction

m-hlevel : ∀ {n} {c : Container}
         → let open Definition c
         in ((i : I) → h n (A i))
         → (i : I) → h n (M i)
m-hlevel {n = 0} hA i = Properties.m-contr hA i
m-hlevel {n = suc n} {c = c} hA i = λ xs ys
  → retract-hlevel mext mext-inv mext-retraction (ih xs ys)
  where
    open Definition c
    open Extensionality c
    open Fixpoint (fix M fixpoint)
      using (head; tail)

    ih : (xs ys : M i) → h n (xs ≡M ys)
    ih xs ys = m-hlevel (λ { (i , xs , ys) → hA i (head xs) (head ys) })
                        (i , xs , ys)
