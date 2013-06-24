{-# OPTIONS --without-K #-}

module category.functor.properties where

open import function.core
open import equality.core
open import category.category
open import category.functor.core
open import category.functor.hlevel
open import category.functor.ops

func-left-unit : {C D : Category}
                 (F : Functor C D)
               → id ∘ F ≡ F
func-left-unit F = func-equality refl

func-right-unit : {C D : Category}
                 (F : Functor C D)
               → F ∘ id ≡ F
func-right-unit F = func-equality refl

func-assoc : {B C D E : Category}
             (F : Functor D E) (G : Functor C D) (H : Functor B C)
           → (F ∘ G) ∘ H ≡ F ∘ (G ∘ H)
func-assoc F G H = func-equality refl
