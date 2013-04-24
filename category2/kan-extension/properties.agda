{-# OPTIONS --without-K #-}

open import category2.category
open import category2.functor.core

module category2.kan-extension.properties {i₀ j₀ i₁ j₁ i₂ j₂ i₃ j₃}
  {C : Category i₀ j₀}{C' : Category i₁ j₁}
  {D : Category i₂ j₂}{D' : Category i₃ j₃} where

open import function.core
open import category2.functor.hlevel
open import category2.functor.properties
open import category2.functor.ops
open import category2.kan-extension.core
open import category2.trans
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
