{-# OPTIONS --without-K #-}

module overloading.function {i j}{X : Set i}{Y : Set j} where

open import level
open import sum
open import overloading.core
open import function.isomorphism.core
  hiding (apply)

fun-is-fun : Overload _ (X → Y)
fun-is-fun = overload-self _

inj-is-fun : Overload _ (X → Y)
inj-is-fun = record
  { Source = X ↣ Y
  ; coerce = proj₁ }

private
  module fun-methods {k} ⦃ o : Overload k (X → Y) ⦄ where
    open Overload o public using ()
      renaming (coerce to apply)
open fun-methods public
