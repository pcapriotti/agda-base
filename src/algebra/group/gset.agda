module algebra.group.gset where

open import level
open import algebra.group.core
open import algebra.monoid.mset

module _ {i}(G : Set i) ⦃ gG : IsGroup G ⦄ where
  IsGSet : ∀ {j}(X : Set j) → Set (i ⊔ j)
  IsGSet X = IsMSet G X

  open IsMSet ⦃ ... ⦄

  module _ {j k}
           {X : Set j} ⦃ xG : IsGSet X ⦄
           {Y : Set k} ⦃ yG : IsGSet Y ⦄ where
    IsGSetMorphism : (X → Y) → Set (i ⊔ j ⊔ k)
    IsGSetMorphism = IsMSetMorphism G
