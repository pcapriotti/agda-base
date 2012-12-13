{-# OPTIONS --without-K #-}
open import equality.solver.core
module equality.solver.term {i k}(X : Set i)(W : Graph X k) where

open import level using (_⊔_)
open import equality.core
open import equality.calculus

data Term : Graph X (i ⊔ k) where
  null : ∀ {x} → Term x x
  var : ∀ {x y} → W x y → Term x y
  _*_ : ∀ {x y z} → Term y z → Term x y → Term x z
  inv : ∀ {x y} → Term y x → Term x y
infixl 5 _*_

module WithEnv (env : Env W) where
  eval : ∀ {x y} → Term x y → x ≡ y
  eval null = refl
  eval (var x) = env x
  eval (g * f) = eval f ⊚ eval g
  eval (inv t) = eval t ⁻¹