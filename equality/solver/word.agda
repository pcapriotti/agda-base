{-# OPTIONS --without-K #-}
open import equality.solver.core
module equality.solver.word {i k}(X : Set i)(W : Graph X k) where

open import level using (_⊔_)
open import equality.core
open import equality.calculus

data Word : Graph X (i ⊔ k) where
  fwd : ∀ {x y} → W x y → Word x y
  inv : ∀ {x y} → W y x → Word x y

wreverse : ∀ {x y} → Word x y → Word y x
wreverse (fwd w) = inv w
wreverse (inv w) = fwd w

wreverse-wreverse : ∀ {x y}(w : Word x y)
                  → wreverse (wreverse w) ≡ w
wreverse-wreverse (fwd w) = refl
wreverse-wreverse (inv w) = refl

word-involution : Involution Word
word-involution = record
  { τ = wreverse
  ; τ-τ = wreverse-wreverse }

module WithEnv (env : Env W) where
  eval : Env Word
  eval (fwd w) = env w
  eval (inv w) = env w ⁻¹

  wreverse-inv : ∀ {x y}(w : Word x y)
               → eval (wreverse w)
               ≡ eval w ⁻¹
  wreverse-inv (fwd w) = refl
  wreverse-inv (inv w) = sym (double-inverse (env w))