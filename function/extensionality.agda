{-# OPTIONS --without-K #-}
module function.extensionality where

open import function.extensionality.core public
open import function.extensionality.nondep public
  using (ext; ext-id)
open import function.extensionality.dependent public
  using (ext'; ext-id')
open import function.extensionality.strong public
  using (strong-ext; strong-ext-iso)
