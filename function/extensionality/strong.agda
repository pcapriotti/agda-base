{-# OPTIONS --without-K #-}
module function.extensionality.strong where

open import level
open import sum
open import function
open import equality.core
open import function.isomorphism
open import function.extensionality.core
open import function.extensionality.proof-dep
open import hott.hlevel
open import hott.univalence.properties

private
  module Dummy {i j}(X : Set i)(Y : X → Set j)
               (ext : Extensionality' i j)
               (Π-contr : ∀ {i j} {X : Set i}{Y : X → Set j}
                        → ((x : X) → contr (Y x))
                        → contr ((x : X) → Y x))
               (ext-id : (f : (x : X) → Y x) → ext f f (λ _ → refl) ≡ refl) where

    _~_ : (f g : (x : X) → Y x) → Set (i ⊔ j)
    f ~ g = ∀ x → f x ≡ g x
    infix 5 _~_

    R : (f : (x : X) → Y x) → f ~ f
    R f x = refl

    happly : {f g : (x : X) → Y x} → f ≡ g → f ~ g
    happly refl x = refl

    ext-happly : {f g : (x : X) → Y x} (p : f ≡ g)
               → ext f g (happly p) ≡ p
    ext-happly {f} refl = ext-id f

    happly-ext : (f g : (x : X) → Y x) (h : f ~ g)
               → happly (ext f g h) ≡ h
    happly-ext f g h = subst (λ {(g , h) → happly (ext f g h) ≡ h})
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
          (Π-contr (λ x → singl-contr (f x)))

        e-contr' : (u : E) → (f , R f) ≡ u
        e-contr' u = contr⇒isProp e-contr (f , R f) u

        strong-id : happly (ext f f (R f)) ≡ R f
        strong-id = cong happly (ext-id f)

    ext-iso : (f g : (x : X) → Y x)
            → (f ~ g) ≅ (f ≡ g)
    ext-iso f g = iso (ext f g) happly (happly-ext f g) ext-happly

  module Dummy' {i j} where
    strong-ext : StrongExt i j
    strong-ext {X = X}{Y} f g = ≅⇒≡ (ext-iso f g)
      where
        open Dummy X Y extensionality' (Π-contr extensionality') ext-id'

open Dummy' public
