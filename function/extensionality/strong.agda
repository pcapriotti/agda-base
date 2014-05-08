{-# OPTIONS --without-K --type-in-type #-}
module function.extensionality.strong where

open import level
open import sum
open import function.core
open import equality.core
open import function.isomorphism
open import function.extensionality.core
open import function.extensionality.proof
open import hott.hlevel.core
open import hott.hlevel.closure.core
open import hott.weak-equivalence.core

private
  module Dummy {X : Set}{Y : X → Set} where
    _~_ : (f g : (x : X) → Y x) → Set
    f ~ g = ∀ x → f x ≡ g x
    infix 5 _~_

    R : (f : (x : X) → Y x) → f ~ f
    R f x = refl

    iso₁ : {f g : (x : X) → Y x} (p : f ≡ g)
         → funext (funext-inv p) ≡ p
    iso₁ {f} refl = funext-id f

    iso₂ : (f g : (x : X) → Y x) (h : f ~ g)
         → funext-inv (funext h) ≡ h
    iso₂ f g h = subst (λ {(g , h) → funext-inv (funext h) ≡ h})
                       (e-contr' (g , h))
                       strong-id
      where
        E : Set
        E = Σ ((x : X) → Y x) λ g → f ~ g

        e-contr : contr E
        e-contr = retract-hlevel
          (λ u → proj₁ ∘' u , proj₂ ∘' u)
          (λ {(g , h) x → g x , h x})
          (λ {(g , h) → refl})
          (Π-contr (λ x → singl-contr (f x)))

        e-contr' : (u : E) → (f , R f) ≡ u
        e-contr' u = contr⇒prop e-contr (f , R f) u

        strong-id : funext-inv (funext (R f)) ≡ R f
        strong-id = ap funext-inv (funext-id f)

    strong-funext-iso : {f g : (x : X) → Y x}
                   → (f ~ g) ≅ (f ≡ g)
    strong-funext-iso {f}{g} = iso funext funext-inv (iso₂ f g) iso₁

    strong-funext : {f g : (x : X) → Y x} → (f ~ g) ≡ (f ≡ g)
    strong-funext = ≅⇒≡ strong-funext-iso

open Dummy public using (strong-funext; strong-funext-iso)
