{-# OPTIONS --without-K #-}
module equality.reasoning where

open import equality.core
open import equality.groupoid

module ≡-Reasoning {i} {X : Set i} where
  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≡⟨_⟩_
  infix  1 begin_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : X) : Set i where
    relTo : x ≡ y → x IsRelatedTo y

  begin_ : ∀ {x y} → x IsRelatedTo y → x ≡ y
  begin relTo p = p

  _≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ p ⟩ relTo q = relTo (trans p q)

  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo refl