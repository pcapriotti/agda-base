{-# OPTIONS --without-K #-}

module category.functor where

open import category.category
open import function using () renaming (id to ι ; _∘_ to _⋆_)
open import level using (_⊔_)
open import equality.core using (_≡_ ; refl ; cong)

record Functor {i j i' j'}
               (C : Category i j)
               (D : Category i' j')
             : Set (i ⊔ j ⊔ i' ⊔ j') where
  constructor functor

  open Category hiding (hom ; id ; _∘_)
  open Category C using (hom ; id ; _∘_)
  open Category D using ()
    renaming ( hom to hom'
             ; id to id'
             ; _∘_ to _∘'_ )

  field apply : obj C → obj D
  private F = apply
  field map : {X Y : obj C}
            → hom X Y → hom' (F X) (F Y)

  field
    map-id : (X : obj C)
           → map (id X) ≡ id' (F X)
    map-hom : {X Y Z : obj C}
              (f : hom X Y)(g : hom Y Z)
            → map (g ∘ f) ≡ map g ∘' map f

Id : ∀ {i j}(C : Category i j) → Functor C C
Id C = record
  { apply = ι
  ; map = ι
  ; map-id = λ _ → refl
  ; map-hom = λ _ _ → refl }

Compose : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
          {C : Category i₁ j₁}
          {D : Category i₂ j₂}
          {E : Category i₃ j₃}
        → Functor D E
        → Functor C D
        → Functor C E
Compose {C = C} {D} {E} F G = record
  { apply = apply F ⋆ apply G
  ; map = map F ⋆ map G
  ; map-id = λ X → begin
        map F (map G (id₁ _))
      ≡⟨ cong (map F) (map-id G X) ⟩
        map F (id₂ _)
      ≡⟨ map-id F _ ⟩
        id₃ _
      ∎
  ; map-hom = λ f g → begin
        map F (map G (g ∘₁ f))
      ≡⟨ cong (map F) (map-hom G f g) ⟩
        map F (map G g ∘₂ map G f)
      ≡⟨ map-hom F (map G f) (map G g) ⟩
        map F (map G g) ∘₃ map F (map G f)
      ∎ }
  where
    open import equality.reasoning
    open ≡-Reasoning

    open Category hiding (hom ; id ; _∘_)
    open Category C using ()
      renaming ( hom to hom₁
               ; id to id₁
               ; _∘_ to _∘₁_ )
    open Category D using ()
      renaming ( hom to hom₂
               ; id to id₂
               ; _∘_ to _∘₂_ )
    open Category E using ()
      renaming ( hom to hom₃
               ; id to id₃
               ; _∘_ to _∘₃_ )
    open Functor
