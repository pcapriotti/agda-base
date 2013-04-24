{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import equality.calculus using (_⊚_)
open import function.core
open import function.isomorphism
open import function.extensionality
open import function.overloading
open import category2.structure
open import category2.graph
open import category2.category
open import category2.functor
open import category2.trans
open import category2.trans.hlevel
open import category2.instances.set

module category2.yoneda {i j}(C : Category i j) where

open as-category C

hom-func : obj C → Functor C (set j)
hom-func X = mk-functor {D = set j} record
  { apply = λ Y → (hom X Y , trunc X Y)
  ; map = _∘_
  ; map-id = λ _ → ext λ x → left-id x
  ; map-hom = λ f g → ext λ x → ? }

hom-map : {X X' : obj C}(f : hom X X') → hom-func X' ⇒ hom-func X
hom-map f = record
  { α = λ Y g → g ∘ f
  ; α-nat = λ h → ext λ g → assoc h g f }

-- Yoneda embedding
y : Functor (op C) (Func C (set j))
y = mk-functor {C = op C}{D = Func C (set j)} record
  { apply = hom-func
  ; map = hom-map
  ; map-id = λ X → nat-equality
      ( ext' λ _ → ext right-id)
  ; map-hom = ? }

-- Yoneda lemma
y-iso : (X : obj C)(F : Functor C (set j))
      → (hom-func X ⇒ F) ≅ proj₁ (apply F X)
y-iso X F = record
  { to = λ { (nt α _) → α X id }
  ; from = λ u → record
      { α = λ Y f → map F f u
      ; α-nat = λ f
              → ext' λ g
              → ext-inv (map-hom F g f) u }
  ; iso₁ = λ { (nt α α-nat)
             → nat-equality
             ( ext' λ Y
             → ext λ f
             → ext-inv (sym (α-nat f)) id
             ⊚ cong (α Y) (right-id f)) }
  ; iso₂ = λ u → ext-inv (map-id F X) u }
