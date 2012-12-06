module function.extensionality.proof-dep where

open import level using (_⊔_; ↑; lift)
open import sets.unit
open import sum
open import equality.core
open import function.extensionality.core
open import function.extensionality.proof
open import function using (_∘_; const)

open import hott.hlevel using
  (contr; singl-contr; contr⇒isProp)
open import hott.univalence.properties

-- assume contractible spaces are closed under Π
private
  module Π-Contractible
    (Π-contr : ∀ {i j} {X : Set i}{Y : X → Set j}
             → ((x : X) → contr (Y x))
             → contr ((x : X) → Y x)) where

    extensionality' : ∀ {i j} → Extensionality' i j
    extensionality' {i} {j} {X = X} {Y = Y} f g h = cong (λ u → proj₁ ∘ u) p
      where
        U : (x : X) → Set _
        U x = singleton (f x)

        U-contr : contr ((x : X) → U x)
        U-contr = Π-contr (λ x → singl-contr (f x))

        f* : (x : X) → U x
        f* x = f x , refl

        g* : (x : X) → U x
        g* x = g x , h x

        p : f* ≡ g*
        p = contr⇒isProp U-contr f* g*

open Π-Contractible (Π-contr extensionality) public