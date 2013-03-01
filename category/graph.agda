{-# OPTIONS --without-K #-}

module category.graph where

open import level
open import sum

record Graph i j : Set (lsuc (i ⊔ j)) where
  constructor graph
  field
    obj : Set i
    hom : obj → obj → Set j

  total : Set (i ⊔ j)
  total = Σ (obj × obj) (uncurry hom)

record Morphism {i j i' j'}
                (G : Graph i j)
                (H : Graph i' j')
              : Set (i ⊔ i' ⊔ j ⊔ j') where
  constructor morphism
  open Graph
  field
    apply : obj G → obj H
    map : ∀ {x y} → hom G x y → hom H (apply x) (apply y)
