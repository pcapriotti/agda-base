{-# OPTIONS --without-K #-}

open import equality.core
open import equality.calculus
open import function.core
open import function.extensionality
open import function.overloading
open import category.category
open import category.graph
open import category.functor
open import category.trans.core
open import category.trans.hlevel
open import category.trans.properties

module category.trans.horizontal {i₀}{j₀}{i₁}{j₁}{i₂}{j₂}
  {C : Category i₀ j₀}{D : Category i₁ j₁}{E : Category i₂ j₂} where

open as-category E
open as-category (Func C E)

_◂_ : (H : Functor D E){F G : Functor C D}(n : F ⇒ G) → H ∘ F ⇒ H ∘ G
_◂_ H {F}{G} (nt α α-nat) = nt Hα Hα-nat
  where
    Hα : ∀ X → hom (apply H (apply F X)) (apply H (apply G X))
    Hα X = map H (α X)

    Hα-nat : natural (H ∘ F) (H ∘ G) Hα
    Hα-nat f = sym (map-hom H _ _)
             · ap (map H) (α-nat f)
             · map-hom H _ _
infix 5 _◂_

_▸_ : {F G : Functor D E}(n : F ⇒ G)(H : Functor C D) → F ∘ H ⇒ G ∘ H
_▸_ {F}{G} (nt α α-nat) H = nt αH αH-nat
  where
    αH : ∀ X → hom (apply F (apply H X)) (apply G (apply H X))
    αH X = α (apply H X)

    αH-nat : natural (F ∘ H) (G ∘ H) αH
    αH-nat f = α-nat (map H f)
infix 5 _▸_

_◾_ : {F G : Functor D E}(n : F ⇒ G){H K : Functor C D}(m : H ⇒ K)
    → F ∘ H ⇒ G ∘ K
_◾_ {F}{G} n {H}{K} m = (G ◂ m) ∘ (n ▸ H)

_◾'_ : {F G : Functor D E}(n : F ⇒ G){H K : Functor C D}(m : H ⇒ K)
     → F ∘ H ⇒ G ∘ K
_◾'_ {F}{G} n {H}{K} m = (n ▸ K) ∘ (F ◂ m)

interchange : {F G : Functor D E}(n : F ⇒ G){H K : Functor C D}(m : H ⇒ K)
            → n ◾ m ≡ n ◾' m
interchange (nt _ α-nat) (nt β _) =
  sym (nat-equality (funext λ X → α-nat (β X)))
