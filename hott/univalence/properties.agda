{-# OPTIONS --without-K #-}
module hott.univalence.properties where

open import function.extensionality
open import hott.hlevel

import hott.univalence.properties.core as Core
open Core public
  hiding (exp-contr; Π-contr; Π-hlevel)

Π-hlevel : ∀ {i j n} {X : Set i}{Y : X → Set j}
         → ((x : X) → h n (Y x))
         → h n ((x : X) → Y x)
Π-hlevel = Core.Π-hlevel strong-ext
