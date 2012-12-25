{-# OPTIONS --without-K #-}
open import equality.solver.core
module equality.solver.term {i}{X : Set i}{k}(W : Graph X k) where

open import level using (_⊔_)
open import equality.core
open import equality.calculus

data Term : Graph X (i ⊔ k) where
  null : ∀ {x} → Term x x
  var : ∀ {x y} → W x y → Term x y
  _*_ : ∀ {x y z} → Term x y → Term y z → Term x z
  inv : ∀ {x y} → Term y x → Term x y
infixl 5 _*_

module WithEnv {j}{X' : Set j}(env : Env W X') where
  eval : Env Term X'
  eval = record { imap = imap env ; gmap = go }
    where
      go : ∀ {x y} → Term x y → imap env x ≡ imap env y
      go null = refl
      go (var x) = gmap env x
      go (g * f) = go g ⊚ go f
      go (inv t) = go t ⁻¹
