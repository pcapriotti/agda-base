{-# OPTIONS --without-K #-}
open import solver.equality.core
module solver.equality.word {i k}{X : Set i}(W : Graph X k) where

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

word-inv : Involution Word
word-inv = record
  { τ = wreverse
  ; τ-τ = wreverse-wreverse }

module WithEnv {j}{X' : Set j}(env : Env W X') where
  eval : Env Word X'
  eval = record
    { imap = imap env
    ; gmap = λ
      { (fwd w) → gmap env w
      ; (inv w) → gmap env w ⁻¹ } }

  wreverse-inv : ∀ {x y}(w : Word x y)
               → gmap eval (wreverse w)
               ≡ gmap eval w ⁻¹
  wreverse-inv (fwd w) = refl
  wreverse-inv (inv w) = sym (double-inverse (gmap env w))

  word-env-inv : EnvInvolution Word eval
  word-env-inv = record
    { inv = word-inv
    ; τ-correct = wreverse-inv }