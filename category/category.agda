{-# OPTIONS --without-K #-}

module category.category where

open import level using (Level ; lsuc ; _⊔_)
open import sum
open import function using (flip)
open import equality.core
open import hott.hlevel

open import category.class

record Category (i j : Level) : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    is-cat : IsCategory obj j

  open IsCategory is-cat

  field
    trunc : ∀ x y → h 2 (hom x y)

  mor : Set (i ⊔ j)
  mor = Σ (obj × obj) (uncurry hom)

  open IsCategory is-cat public

-- opposite category
op : ∀ {i j} → Category i j → Category i j
op C = record
  { obj = obj
  ; is-cat = record
    { hom = flip hom
    ; id = id
    ; _∘_ = flip _∘_
    ; left-unit = right-unit
    ; right-unit = left-unit
    ; associativity = λ f g h → sym (associativity h g f) }
  ; trunc = flip trunc }
  where
    open Category C

-- interface

open Category public using (obj; mor; trunc)
private
  module Interface {i j} ⦃ C : Category i j ⦄ where
    open Category C using (is-cat)
    open IsCategory is-cat public
open Interface public
