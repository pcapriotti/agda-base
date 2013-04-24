{-# OPTIONS --without-K #-}

module category2.structure where

open import level

record Structure {s o i} (Struct : Set o → Set i) :
       Set (lsuc (s ⊔ o ⊔ i)) where
  field
    Sort : Set s
    obj : Sort → Set o
    struct : (X : Sort) → Struct (obj X)

record IsSubtype {s o i} (Struct : Set o → Set i) :
       Set (lsuc (lsuc (s ⊔ o ⊔ i))) where
  field st : Structure {s} Struct
  open Structure st
  field X : Structure.Sort st

  structure : Struct (obj X)
  structure = struct X

module overloaded {s o i} (Struct : Set o → Set i)
                          ⦃ st : Structure {s} Struct ⦄
                          (X : Structure.Sort st) where
  overloaded-subtype : IsSubtype Struct
  overloaded-subtype = record
    { st = st
    ; X = X }
