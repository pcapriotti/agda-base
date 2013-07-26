{-# OPTIONS --type-in-type --without-K #-}
module solver.equality.core where

open import sum
open import decidable
open import function using (flip)
open import sets.empty
open import sets.fin using (Fin)
open import sets.vec
open import level using (_⊔_)
open import equality.core
open import equality.calculus
open import hott.hlevel

IEnv : (X : Set) → ∀ n → Set
IEnv X n = Vec X n

Edges : (X : Set) → Set
Edges X = X → X → Set

record _⇒_ {X X' : Set}
            (W : Edges X)(U : Edges X') : Set where
  field
    imap : X → X'
    gmap : ∀ {x y} → W x y → U (imap x) (imap y)
infixr 2 _⇒_
open _⇒_ public

Env : {X : Set} → Edges X → Set → Set
Env W X' = W ⇒ (_≡_ {A = X'})

total-space : {X : Set} → Edges X → Set
total-space {X = X} W = Σ (X × X) (uncurry W)

lift-total : {X : Set}(W : Edges X)
           → ∀ {x y} → W x y → total-space W
lift-total W {x}{y} w = ((x , y) , w)

record Involution {X : Set}(W : Edges X) : Set where
  field
    τ : ∀ {x y} → W x y → W y x
    τ-τ : ∀ {x y}(w : W x y) → τ (τ w) ≡ w

record EnvInvolution {X : Set}{X' : Set}
                     (W : Edges X) (env : Env W X') : Set where
  field
    inv : Involution W

  open Involution inv

  field
    τ-correct : ∀ {x y}(w : W x y)
              → gmap env (τ w) ≡ sym (gmap env w)

  open Involution inv public

record DecGraph {X : Set}(W : Edges X) : Set where
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

dec-total : {X : Set}{W : Edges X}
          → ((x y : X) → Dec (x ≡ y))
          → ((w w' : total-space W) → Dec (w ≡ w'))
          → DecGraph W
dec-total {X = X} {W = W} idec tdec = record { idec = idec ; gdec = dec' }
  where
    dec' : ∀ {x y} → (w w' : W x y) → Dec (w ≡ w')
    dec' {x}{y} w w' with tdec ((x , y) , w) ((x , y) , w')
    ... | yes p = yes (subst (λ q₀ → subst (uncurry W) q₀ w ≡ w') q₀-trivial q₁)
      where
        q₀ : (x , y) ≡ (x , y)
        q₀ = proj₁ (congΣ p)

        q₁ : subst (uncurry W) q₀ w ≡ w'
        q₁ = proj₂ (congΣ p)

        dec₂ : (p p' : X × X) → Dec (p ≡ p')
        dec₂ (x , y) (x' , y') with idec x x' | idec y y'
        ... | no f | _ = no (λ q → f (cong proj₁ q))
        ... | yes _ | no f = no (λ q → f (cong proj₂ q))
        dec₂ (x , y) (.x , .y) | yes refl | yes refl = yes refl

        h2 : h 2 (X × X)
        h2 = hedberg dec₂

        q₀-trivial : q₀ ≡ refl
        q₀-trivial = proj₁ (h2 (x , y) (x , y) q₀ refl)
    ... | no f = no (λ p → f (lift p))
      where
        lift : ∀ {x y}{w w' : W x y} → w ≡ w' → ((x , y) , w) ≡ ((x , y) , w')
        lift refl = refl
