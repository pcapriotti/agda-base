
{-# OPTIONS --without-K  #-}

module base_types.bool where

open import base_types.empty     using (⊥)
open import base_types.unit      using (⊤)
open import decidable using (Dec; yes; no)
open import equality             using (_≡_; refl)
open import level     using (Level)

infixr 6 _∧_
infixr 5 _∨_ _xor_
infix  0 if_then_else_

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true  = false
not false = true

T : Bool → Set
T true  = ⊤
T false = ⊥

if_then_else_ : {a : Level} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

_≟_ : (a b : Bool) → Dec (a ≡ b)
true  ≟ true  = yes refl
false ≟ false = yes refl
true  ≟ false = no λ ()
false ≟ true  = no λ ()
