{-# OPTIONS --without-K #-}

module category2.limit.properties where

open import category2.category
open import category2.functor
open import category2.limit.core
open import category2.kan-extension
open import category2.kan-extension.properties
open import category2.instances.unit

-- a functor preserves a limit if it preserves
-- the corresponding Kan extension
preserves-lim : ∀ {i₀ j₀ i₁ j₁ i₂ j₂}
                {J : Category i₀ j₀}
                {C : Category i₁ j₁}
                {D : Category i₂ j₂}
                {K : Functor J C}
              → Functor C D → Lim K → Set _
preserves-lim {J = J}{C}{D}{K} F lim = preserves-kan F (ran)
  where open Lim lim
