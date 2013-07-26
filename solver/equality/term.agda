{-# OPTIONS --type-in-type --without-K #-}
open import solver.equality.core
module solver.equality.term {X : Set}(W : Edges X) where

open import level using (_⊔_)
open import equality.core
open import equality.calculus

data Term : Edges X where
  null : ∀ {x} → Term x x
  var : ∀ {x y} → W x y → Term x y
  _*_ : ∀ {x y z} → Term x y → Term y z → Term x z
  inv : ∀ {x y} → Term y x → Term x y
infixl 5 _*_

module WithEnv {X' : Set}(env : Env W X') where
  eval : Env Term X'
  eval = record { imap = imap env ; gmap = go }
    where
      go : ∀ {x y} → Term x y → imap env x ≡ imap env y
      go null = refl
      go (var x) = gmap env x
      go (g * f) = go g ⊚ go f
      go (inv t) = go t ⁻¹
