{-# OPTIONS --without-K #-}

module function.overloading {i j}{X : Set i}{Y : Set j} where

open import level
open import sum
open import overloading.core

fun-is-fun : Coercion (X → Y) (X → Y)
fun-is-fun = coerce-self _

private
  module fun-methods {k}{Source : Set k}
                     ⦃ c : Coercion Source (X → Y) ⦄ where
    open Coercion c public using ()
      renaming (coerce to apply)
open fun-methods public
