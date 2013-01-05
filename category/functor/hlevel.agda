{-# OPTIONS --without-K #-}

open import category.category renaming (_∘_ to _⋆_)

module category.functor.hlevel {i j i' j'}
  {C : Category i j}{D : Category i' j'} where

open import level
open import sum
open import category.functor.core
open import category.trans.core
  using (_⇒_) renaming (Id to Idn)
open import equality.core
open import equality.calculus using (uncongΣ)
open import function.extensionality
open import function.isomorphism
  using (_≅_; module _≅_; iso⇒inj)
open import hott.hlevel

open Functor

-- a "lawless" functor
record Mapping : Set (i ⊔ i' ⊔ j ⊔ j') where
  constructor mapping
  field
    m₀ : obj C → obj D
    m₁ : ∀ {X Y} → hom X Y → hom (m₀ X) (m₀ Y)

func-to-mapping : Functor C D → Mapping
func-to-mapping F = mapping (apply F) (map F)

private
  -- the condition on a mapping for being a functor
  Functorial : Mapping → Set _
  Functorial (mapping m₀ m₁) =
      ( ∀ X → m₁ (id X) ≡ id (m₀ X) )
    × ( ∀ X Y Z (g : hom X Y) (f : hom Y Z)
      → m₁ (f ⋆ g) ≡ m₁ f ⋆ m₁ g )

  -- being functorial is a proposition
  func-prop : (m : Mapping) → h 1 (Functorial m)
  func-prop m = ×-hlevel
    ( Π-hlevel λ X → trunc _ _ _ _ )
    ( Π-hlevel λ X
      → Π-hlevel λ Y
      → Π-hlevel λ Z
      → Π-hlevel λ f
      → Π-hlevel λ g
      → trunc _ _ _ _ )

  -- a functor is the same as a functorial mapping
  isom : Functor C D ≅ Σ Mapping Functorial
  isom = record
    { to = λ F → ( func-to-mapping F
                  , (map-id F , λ X Y Z → map-hom F {X}{Y}{Z}) )
    ; from = λ { (mapping m₀ m₁ , (m-id , m-hom))
               → functor m₀ m₁ m-id (m-hom _ _ _) }
    ; iso₁ = λ _ → refl
    ; iso₂ = λ _ → refl
    }

func-equality : {F G : Functor C D}
              → func-to-mapping F ≡ func-to-mapping G
              → F ≡ G
func-equality {F}{G} p = iso⇒inj isom _ _ mappings≡
  where
    open _≅_ isom

    mappings≡ : to F ≡ to G
    mappings≡ = uncongΣ
      (p , h1⇒prop (func-prop (func-to-mapping G)) _ _)

func-coerce : {F G : Functor C D} → F ≡ G → F ⇒ G
func-coerce {F}{.F} refl = Idn F
