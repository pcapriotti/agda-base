{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import equality.calculus using (_⊚_)
open import function.isomorphism
  using (_≅_; iso)
open import function.extensionality
open import category.category
  renaming (_∘_ to _⋆_)
open import category.functor
open import category.trans
  using (_⇒_; nt)
open import category.trans.hlevel
  using (nat-equality)
open import category.instances.set

module category.yoneda {i j}(C : Category i j) where

open Functor

hom-func : obj C → Functor C (set j)
hom-func X = record
  { morph = record
    { apply = λ Y → (hom X Y , trunc C X Y)
    ; map = _⋆_ }
  ; is-func = record
    { map-id = λ _ → ext λ x → left-unit x
    ; map-hom = λ f g → ext λ x → associativity x f g } }

hom-map : {X X' : obj C}(f : hom X X') → hom-func X' ⇒ hom-func X
hom-map f = record
  { α = λ Y g → g ⋆ f
  ; α-nat = λ h → ext λ g → associativity f g h }

-- Yoneda embedding
y : Functor (op C) (Func C (set j))
y = record
  { morph = record
    { apply = hom-func
    ; map = hom-map }
  ; is-func = record
    { map-id = λ X → nat-equality
        ( ext' λ _ → ext right-unit)
    ; map-hom = λ g f → nat-equality
        ( ext' λ _ → ext λ h
        → sym (associativity f g h) ) } }

-- Yoneda lemma
y-iso : (X : obj C)(F : Functor C (set j))
      → (hom-func X ⇒ F) ≅ proj₁ (apply F X)
y-iso X F = record
  { to = λ { (nt α _) → α X (id X) }
  ; from = λ u → record
      { α = λ Y f → map F f u
      ; α-nat = λ f
              → ext' λ g
              → ext-inv (map-hom F g f) u }
  ; iso₁ = λ { (nt α α-nat)
             → nat-equality
             ( ext' λ Y
             → ext λ f
             → ext-inv (sym (α-nat f)) (id X)
             ⊚ cong (α Y) (right-unit f)) }
  ; iso₂ = λ u → ext-inv (map-id F X) u }
