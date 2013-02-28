{-# OPTIONS --without-K #-}

open import category.category renaming (_∘_ to _⋆_)

module category.functor.hlevel {i j i' j'}
  {C : Category i j}{D : Category i' j'} where

open import level
open import sum
import category.graph as Graph
open import category.functor.class
open import category.functor.core
open import category.trans.core
  using (_⇒_) renaming (Id to Idn)
open import equality.core
open import equality.calculus using (uncongΣ)
open import function.extensionality
open import function.isomorphism
  using (_≅_; module _≅_; iso⇒inj)
open import hott.hlevel

open Category using (graph; is-cat)
open Functor

private
  Morphism : Set _
  Morphism = Graph.Morphism (graph C) (graph D)

  Functorial : Morphism → Set _
  Functorial = IsFunctor (is-cat C) (is-cat D)

  is-func-prop : (m : Morphism) → h 1 (Functorial m)
  is-func-prop m = iso-hlevel
    ( record
        { to = uncurry is-functor
        ; from = λ {(is-functor i h) → (i , h) }
        ; iso₁ = λ _ → refl
        ; iso₂ = λ _ → refl } )
    ( ×-hlevel
      ( Π-hlevel λ X → trunc D _ _ _ _ )
      ( Π-hlevel-impl λ X
        → Π-hlevel-impl λ Y
        → Π-hlevel-impl λ Z
        → Π-hlevel λ f
        → Π-hlevel λ g
        → trunc D _ _ _ _ ) )

  isom : Functor C D ≅ Σ Morphism Functorial
  isom = record
    { to = λ F → ( morph F , is-func F )
    ; from = λ { (m , f) → functor m f }
    ; iso₁ = λ _ → refl
    ; iso₂ = λ _ → refl }

func-equality : {F G : Functor C D}
              → morph F ≡ morph G
              → F ≡ G
func-equality {F}{G} p = iso⇒inj isom _ _ morphisms≡
  where
    open _≅_ isom

    morphisms≡ : to F ≡ to G
    morphisms≡ = uncongΣ
      (p , h1⇒prop (is-func-prop (morph G)) _ _)

func-coerce : {F G : Functor C D} → F ≡ G → F ⇒ G
func-coerce {F}{.F} refl = Idn F
