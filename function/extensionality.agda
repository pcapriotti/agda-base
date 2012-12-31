{-# OPTIONS --without-K #-}
module function.extensionality where

open import function.extensionality.core public
open import function.extensionality.proof public using (ext; ext-id)
open import function.extensionality.proof-dep public using (ext'; ext-id')
open import function.extensionality.strong public
  using (strong-ext; strong-ext-iso)
