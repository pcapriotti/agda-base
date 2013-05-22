{-# OPTIONS --without-K #-}

module function.overloading {X : Set}{Y : Set} where

open import level
open import sum
open import overloading.core

fun-is-fun : Coercion (X → Y) (X → Y)
fun-is-fun = coerce-self _

private
  module fun-methods {Source : Set}
                     ⦃ c : Coercion Source (X → Y) ⦄ where
    open Coercion c public using ()
      renaming (coerce to apply)
open fun-methods public
