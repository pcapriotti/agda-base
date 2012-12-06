{-# OPTIONS --without-K #-}
module level where

infixl 5 _⊔_

postulate
  Level : Set
  lzero  : Level
  lsuc   : Level → Level
  _⊔_    : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

record ↑ {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open ↑ public