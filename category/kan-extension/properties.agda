{-# OPTIONS --without-K #-}

open import category.category
open import category.functor.core

module category.kan-extension.properties {C C' D D' : Category} where

open import function.core
open import category.functor.hlevel
open import category.functor.properties
open import category.functor.ops
open import category.kan-extension.core
open import category.trans
open import hott.hlevel

open as-category₀ (Func₀ C D')

kan-map : {K : Functor C C'}{G : Functor C D}(H : Functor D D')
        → Extension K G → Extension K (H ∘ G)
kan-map {K}{G} H (extension F counit) = extension (H ∘ F) counit'
  where
    counit' : (H ∘ F) ∘ K ⇒ H ∘ G
    counit' = (H ◂ counit) ∘ func-coerce (func-assoc H F K)

-- a functor preserves a Kan extension if it maps it to
-- a Kan extension for the composite functor
preserves-kan : {K : Functor C C'}{G : Functor C D}
              → Functor D D' → Ran K G → Set _
preserves-kan {K}{G} H ran = (ext' : Extension K (H ∘ G))
                           → contr (ExtUniv (kan-map H ext) ext')
  where
    open Ran ran
