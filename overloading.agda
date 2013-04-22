{-# OPTIONS --without-K #-}
module overloading where

open import level

record default : Set where
record additive : Set where

record Bundle {i j} {Base : Set i}
                    (Struct : Base → Set j) : Set (lsuc (i ⊔ j)) where
  constructor bundle
  field
    parent : Base
    struct : Struct parent

record Overload i {j} (Target : Set j) : Set (lsuc (i ⊔ j)) where
  constructor overload
  field
    Source : Set i
    coerce : Source → Target

open Overload public

record OverloadInstance i {j}
                        (style : Set)
                        (Target : Set j) : Set (lsuc (i ⊔ j)) where
  field o : Overload i Target

  field source : Source o

  target : Target
  target = coerce o source

module overload {i j}
                (style : Set)
                (Target : Set j)
                ⦃ o : Overload i Target ⦄
                (X : Source o) where
  _instance : OverloadInstance i style Target
  _instance = record
    { o = o
    ; source = X }

overload-self : ∀ {i} (X : Set i) → Overload _ X
overload-self {i} X = record
  { Source = X
  ; coerce = λ x → x }

overload-parent : ∀ {i j k}
       → {X : Set j}
       → ⦃ o : Overload i X ⦄
       → (Source o → Set k)
       → Overload _ X
overload-parent ⦃ o ⦄ Struct = record
  { Source = Bundle Struct
  ; coerce = λ x → coerce o (Bundle.parent x) }

set-is-set : ∀ {i} → Overload _ (Set i)
set-is-set {i} = overload-self _

∣_∣ : ∀ {i j} ⦃ o : Overload i (Set j) ⦄ → Source o → Set j
∣_∣ ⦃ o ⦄ = coerce o
