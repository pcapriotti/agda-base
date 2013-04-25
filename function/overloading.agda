{-# OPTIONS --without-K #-}

module function.overloading {i j}{X : Set i}{Y : Set j} where

open import level
open import sum
open import overloading.core

fun-is-fun : Overload _ (X → Y)
fun-is-fun = overload-self _

private
  module fun-methods {k} ⦃ o : Overload k (X → Y) ⦄ where
    open Overload o public using ()
      renaming (coerce to apply)
open fun-methods public
