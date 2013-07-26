{-# OPTIONS --without-K #-}

module category.limit.properties where

open import category.category
open import category.functor
open import category.limit.core
open import category.kan-extension
open import category.kan-extension.properties
open import category.instances.unit

-- a functor preserves a limit if it preserves
-- the corresponding Kan extension
preserves-lim : {J C D : Category}{K : Functor J C}
              → Functor C D → Lim K → Set _
preserves-lim {J = J}{C}{D}{K} F lim = preserves-kan F (ran)
  where open Lim lim
