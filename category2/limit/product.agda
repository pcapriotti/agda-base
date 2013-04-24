{-# OPTIONS --without-K #-}

module category2.limit.product where

open import sum
open import category2.graph
open import category2.category
open import category2.functor
open import category2.instances.discrete
open import category2.limit.core
open import sets.fin
open import sets.unit
open import sets.vec
open import hott.hlevel

product-graph : Category _ _
product-graph = discrete-cat (Fin 2 , h! (fin-set 2))

private
  module Definition {i j}{C : Category i j} where
    product-diagram : obj C → obj C → Functor product-graph C
    product-diagram X Y = discrete-lift (lookup (X ∷ Y ∷ []))

    Product : obj C → obj C → Set _
    Product A B = Lim (product-diagram A B)

open Definition public
