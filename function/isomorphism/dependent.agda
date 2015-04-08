{-# OPTIONS --without-K #-}
module function.isomorphism.dependent where

open import level
open import equality
open import function.isomorphism.core
open import function.overloading

module _ {i i' j j'}{A : Set i}{A' : Set i'}(φ : A ≅ A') where
  record Dep≅ (B : A → Set j) (B' : A' → Set j') : Set (i ⊔ i' ⊔ j ⊔ j') where
    field
      to : {a' : A'} → B (invert φ a') → B' a'
      from : {a : A} → B' (apply φ a) → B a
      iso₁ : (a : A)(b : B a) → from (to (subst B (sym (_≅_.iso₁ φ a)) b)) ≡ b
      iso₂ : (a' : A')(b' : B' a') → to (from (subst B' (sym (_≅_.iso₂ φ a')) b')) ≡ b'

-- module _ {i i' j j'}{A : Set i}{A' : Set i'}(φ : A ≅ A') where
--   module _ {B : A → Set j}{B' : A' → Set j'} where
--     symDep≅ : Dep≅ φ B B' → Dep≅ (sym≅ φ) B' B
--     symDep≅ ψ = record
--       { to = λ {a'} b' → Dep≅.from ψ b'
--       ; from = {!!}
--       ; iso₁ = {!!}
--       ; iso₂ = {!!} }

--  nondep≅ : {B : A → Set j}{B' : A' → Set j'}
--          → ((a' : A') → B (invert φ a') ≅ B' a')
--          → Dep≅ B B'
--  nondep≅ ψ = record
--    { to = λ b → {!!}
--    ; from = λ {a'} b' → invert (ψ a') b'
--    ; iso₁ = {!!}
--    ; iso₂ = {!!} }
