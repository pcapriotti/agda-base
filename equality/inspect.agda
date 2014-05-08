{-# OPTIONS --without-K  #-}
module equality.inspect where

open import equality.core

data _of_is_ {A : Set}{B : A → Set}
            (f : (x : A) → B x)(x : A)(y : B x) : Set where
  [_] : f x ≡ y → f of x is y

inspect : {A : Set}{B : A → Set}
        → (f : (x : A)→ B x)(x : A)
        → f of x is f x
inspect f x = [ refl ]
