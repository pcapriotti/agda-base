{-# OPTIONS --without-K #-}
module function.extensionality.strong where

open import level
open import sum
open import function
open import equality.core
open import function.isomorphism
open import function.extensionality.core
open import function.extensionality.proof
open import function.extensionality.proof-dep
open import hott.hlevel
open import hott.univalence.properties.core
open import hott.weak-equivalence

private
  module Dummy {i j}{X : Set i}{Y : X → Set j} where
    _~_ : (f g : (x : X) → Y x) → Set (i ⊔ j)
    f ~ g = ∀ x → f x ≡ g x
    infix 5 _~_

    R : (f : (x : X) → Y x) → f ~ f
    R f x = refl

    ext-ext-apply : {f g : (x : X) → Y x} (p : f ≡ g)
               → ext' (ext-apply p) ≡ p
    ext-ext-apply {f} refl = ext-id' f

    ext-apply-ext : (f g : (x : X) → Y x) (h : f ~ g)
               → ext-apply (ext' h) ≡ h
    ext-apply-ext f g h = subst (λ {(g , h) → ext-apply (ext' h) ≡ h})
                         (e-contr' (g , h))
                         strong-id
      where
        E : Set (i ⊔ j)
        E = Σ ((x : X) → Y x) λ g → f ~ g

        e-contr : contr E
        e-contr = retract-contr
          (λ u → proj₁ ∘ u , proj₂ ∘ u)
          (λ {(g , h) x → g x , h x})
          (λ {(g , h) → refl})
          (Π-contr ext (λ x → singl-contr (f x)))

        e-contr' : (u : E) → (f , R f) ≡ u
        e-contr' u = contr⇒prop e-contr (f , R f) u

        strong-id : ext-apply (ext' (R f)) ≡ R f
        strong-id = cong ext-apply (ext-id' f)

    strong-ext-iso : {f g : (x : X) → Y x}
                   → (f ~ g) ≅ (f ≡ g)
    strong-ext-iso {f}{g} = iso ext' ext-apply (ext-apply-ext f g) ext-ext-apply

    strong-ext : {f g : (x : X) → Y x} → (f ~ g) ≡ (f ≡ g)
    strong-ext = ≅⇒≡ strong-ext-iso

open Dummy public using (strong-ext; strong-ext-iso)
