{-# OPTIONS --without-K #-}
module function.extensionality.strong where

open import level
open import sum
open import function.core
open import equality.core
open import function.isomorphism
open import function.extensionality.core
open import function.extensionality.nondep
open import function.extensionality.dependent
open import hott.hlevel.core
open import hott.hlevel.properties
open import hott.weak-equivalence.core
open import hott.weak-equivalence.conversion

private
  module Dummy {i j}{X : Set i}{Y : X → Set j} where
    _~_ : (f g : (x : X) → Y x) → Set (i ⊔ j)
    f ~ g = ∀ x → f x ≡ g x
    infix 5 _~_

    R : (f : (x : X) → Y x) → f ~ f
    R f x = refl

    iso₁ : {f g : (x : X) → Y x} (p : f ≡ g)
         → ext' (ext-inv p) ≡ p
    iso₁ {f} refl = ext-id' f

    iso₂ : (f g : (x : X) → Y x) (h : f ~ g)
         → ext-inv (ext' h) ≡ h
    iso₂ f g h = subst (λ {(g , h) → ext-inv (ext' h) ≡ h})
                       (e-contr' (g , h))
                       strong-id
      where
        E : Set (i ⊔ j)
        E = Σ ((x : X) → Y x) λ g → f ~ g

        e-contr : contr E
        e-contr = retract-hlevel
          (λ u → proj₁ ∘ u , proj₂ ∘ u)
          (λ {(g , h) x → g x , h x})
          (λ {(g , h) → refl})
          (Π-contr (λ x → singl-contr (f x)))

        e-contr' : (u : E) → (f , R f) ≡ u
        e-contr' u = contr⇒prop e-contr (f , R f) u

        strong-id : ext-inv (ext' (R f)) ≡ R f
        strong-id = cong ext-inv (ext-id' f)

    strong-ext-iso : {f g : (x : X) → Y x}
                   → (f ~ g) ≅ (f ≡ g)
    strong-ext-iso {f}{g} = iso ext' ext-inv (iso₂ f g) iso₁

    strong-ext : {f g : (x : X) → Y x} → (f ~ g) ≡ (f ≡ g)
    strong-ext = ≅⇒≡ strong-ext-iso

open Dummy public using (strong-ext; strong-ext-iso)
