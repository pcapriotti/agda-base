{-# OPTIONS --without-K #-}
module equality.solver.core where

open import sum
open import decidable
open import function using (flip)
open import sets.empty
open import sets.fin using (Fin)
open import sets.vec
open import level using (_⊔_)
open import equality.core
open import hott.hlevel
open import hott.hlevel.properties.sets

IEnv : ∀ {i} (X : Set i) → ∀ n → Set _
IEnv X n = Vec X n

Graph : ∀ {i} (X : Set i) → ∀ k → Set _
Graph X k = X → X → Set k

record _⇒_ {i j k k'}{X : Set i}{X' : Set j}
            (W : Graph X k)(U : Graph X' k')
          : Set (i ⊔ j ⊔ k ⊔ k') where
  field
    imap : X → X'
    gmap : ∀ {x y} → W x y → U (imap x) (imap y)
infixr 2 _⇒_
open _⇒_ public

Env : ∀ {i j k} {X : Set i} → Graph X k → Set j → Set _
Env W X' = W ⇒ (_≡_ {A = X'})

total-space : ∀ {i k}{X : Set i} → Graph X k → Set _
total-space {X = X} W = Σ (X × X) (uncurry W)

lift-total : ∀ {i k}{X : Set i}(W : Graph X k)
           → ∀ {x y} → W x y → total-space W
lift-total W {x}{y} w = ((x , y) , w)

record Involution {i k}{X : Set i}(W : Graph X k) : Set (i ⊔ k) where
  field
    τ : ∀ {x y} → W x y → W y x
    τ-τ : ∀ {x y}(w : W x y) → τ (τ w) ≡ w

record EnvInvolution {i j k}{X : Set i}{X' : Set j}
                     (W : Graph X k) (env : Env W X')
                   : Set (i ⊔ j ⊔ k) where
  field
    inv : Involution W

  open Involution inv

  field
    τ-correct : ∀ {x y}(w : W x y)
              → gmap env (τ w) ≡ sym (gmap env w)

  open Involution inv public

record DecGraph {i k}{X : Set i}(W : Graph X k) : Set (i ⊔ k) where
  field
    idec : (x y : X) → Dec (x ≡ y)
    gdec : ∀ {x y} → (w u : W x y) → Dec (w ≡ u)

  h2 : h 2 X
  h2 = hedberg idec

  _≟_ : ∀ {x y y'} → (w : W x y)(w' : W x y')
      → Dec (Σ (y ≡ y') λ q → subst (W x) q w ≡ w')
  _≟_ {x}{y}{y'} w w' with idec y y'
  ... | no f = no (λ { (q , _) → f q })
  _≟_ {x}{y}{y'} w w' | yes q with gdec (subst (W x) q w) w'
  ... | yes p = yes (q , p)
  ... | no f = no (λ { (q' , p) → f' q' p })
    where
      f' : (q' : y ≡ y')
         → subst (W x) q' w ≡ w'
         → ⊥
      f' q' p = f (subst (λ q → subst (W x) q w ≡ w') r p)
        where
          r : q' ≡ q
          r = proj₁ (h2 y y' q' q)

  _≟'_ : ∀ {x x' y} → (w : W x y)(w' : W x' y)
      → Dec (Σ (x ≡ x') λ q → subst (flip W y) q w ≡ w')
  _≟'_ {x}{x'}{y} w w' with idec x x'
  ... | no f = no (λ { (q , _) → f q })
  _≟'_ {x}{x'}{y} w w' | yes q with gdec (subst (flip W y) q w) w'
  ... | yes p = yes (q , p)
  ... | no f = no (λ { (q' , p) → f' q' p })
    where
      f' : (q' : x ≡ x')
         → subst (flip W y) q' w ≡ w'
         → ⊥
      f' q' p = f (subst (λ q → subst (flip W y) q w ≡ w') r p)
        where
          r : q' ≡ q
          r = proj₁ (h2 x x' q' q)
