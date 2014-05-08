{-# OPTIONS --without-K #-}
module sets.list.properties where

open import equality.core
open import sets.list.core

module _ {i}{A : Set i} where
  data all {j}(P : A → Set j) : List A → Set (i ⊔ j) where
    mk-all : ∀ {x xs} → P x → all P xs → all P (x ∷ xs)

  data any {j}(P : A → Set j) : List A → Set (i ⊔ j) where
    hd-any : ∀ {x xs} → P x → any P (x ∷ xs)
    tl-any : ∀ {x xs} → any P xs → any P (x ∷ xs)

  elem : A → List A → Set i
  elem x = any (λ x' → x ≡ x')
