{-# OPTIONS --without-K #-}

open import equality.core
open import equality.calculus
  using (_⊚_)
open import category.category
open import category.functor
open import category.functor.category
open import category.trans.core
  using (_⇒_; nt)
open import category.trans.hlevel

module category.limit {i}{j}{i'}{j'}
  (C : Category i j)(J : Category i' j') where

open Category using
  (obj; hom; id; right-unit; left-unit)

Δ : Functor C (Func J C)
Δ = record
  { apply = Const J
  ; map = ConstNat.tr
  ; map-id = λ f → nat-equality _ _ refl
  ; map-hom = λ f g → nat-equality _ _ refl }
  where
    open Category C using ()
      renaming (_∘_ to _⋆_)

    module ConstNat {X X'} (f : hom C X X') where
      α : (Y : obj J) → hom C X X'
      α _ = f

      α-nat : {Y Y' : obj J} (g : hom J Y Y')
            → f ⋆ id C X ≡ id C X' ⋆ f
      α-nat _ = right-unit C f ⊚ sym (left-unit C f)

      tr : Const J X ⇒ Const J X'
      tr = nt α α-nat
