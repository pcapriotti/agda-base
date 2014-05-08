{-# OPTIONS --without-K --type-in-type #-}
module function.isomorphism.core where

open import level using (_⊔_)
open import equality.core
open import equality.groupoid
open import equality.reasoning
open import function.core
open import function.overloading
open import sum
open import overloading.core

-- isomorphisms
record _≅_ (X : Set)(Y : Set) : Set where
  constructor iso
  field
    to : X → Y
    from : Y → X
    iso₁ : (x : X) → from (to x) ≡ x
    iso₂ : (y : Y) → to (from y) ≡ y
infix 5 _≅_

≅-struct-iso : {X : Set}{Y : Set}
             → (X ≅ Y)
             ≅ ( Σ (X → Y) λ f
               → Σ (Y → X) λ g
               → ((x : X) → g (f x) ≡ x)
               × ((y : Y) → f (g y) ≡ y) )
≅-struct-iso = record
  { to = λ { (iso f g α β) → f , g , α , β }
  ; from = λ { (f , g , α , β) → iso f g α β }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl  }

refl≅ : {X : Set} → X ≅ X
refl≅ = iso id id (λ _ → refl) (λ _ → refl)

≡⇒≅ : {X Y : Set} → X ≡ Y → X ≅ Y
≡⇒≅ refl = refl≅

sym≅ : {X : Set}{Y : Set} → X ≅ Y → Y ≅ X
sym≅ (iso f g H K) = iso g f K H

trans≅ : {X : Set}{Y : Set}{Z : Set}
       → X ≅ Y → Y ≅ Z → X ≅ Z
trans≅ {X = X}{Z = Z} (iso f g H K) (iso f' g' H' K') = record
  { to = f' ∘ f
  ; from = g ∘ g'
  ; iso₁ = iso₁
  ; iso₂ = iso₂ }
  where
    abstract
      iso₁ : (x : X) → g (g' (f' (f x))) ≡ x
      iso₁ x = ap g (H' (f x)) · H x

      iso₂ : (z : Z) → f' (f (g (g' z))) ≡ z
      iso₂ y = ap f' (K (g' y)) · K' y

_·≅_ : {X : Set}{Y : Set}{Z : Set}
     → X ≅ Y → Y ≅ Z → X ≅ Z
_·≅_ = trans≅
infixl 9 _·≅_

module ≅-Reasoning where
  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≅⟨_⟩_
  infixr 2 _≡⟨_⟩_
  infix  1 begin_

  data _IsRelatedTo_ (x : Set)(y : Set) : Set where
    relTo : x ≅ y → x IsRelatedTo y

  begin_ : {X : Set}{Y : Set} → X IsRelatedTo Y → X ≅ Y
  begin relTo p = p

  _≅⟨_⟩_ : (X : Set) {Y : Set}{Z : Set}
         → X ≅ Y → Y IsRelatedTo Z → X IsRelatedTo Z
  _ ≅⟨ p ⟩ relTo q = relTo (trans≅ p q)

  _≡⟨_⟩_ : (X : Set) {Y : Set} {Z : Set}
         → X ≡ Y → Y IsRelatedTo Z → X IsRelatedTo Z
  _ ≡⟨ p ⟩ relTo q = relTo (trans≅ (≡⇒≅ p) q)

  _∎ :  (X : Set) → X IsRelatedTo X
  _∎ _ = relTo refl≅

injective : {X : Set}{Y : Set}
          → (f : X → Y) → Set
injective f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

surjective : {X : Set}{Y : Set}
           → (f : X → Y) → Set
surjective {X = X}{Y = Y} f = (y : Y) → Σ X λ x → f x ≡ y

_↣_ : Set → Set → Set
A ↣ B = Σ (A → B) injective

-- composition of injections:
_∘i_ : {A : Set}{B : Set}{C : Set}
     → (B ↣ C) → (A ↣ B) → (A ↣ C)
(g , p) ∘i (f , q) = g ∘ f , q ∘ p

_↠_ : Set → Set → Set
A ↠ B = Σ (A → B) surjective

private
  module properties {X : Set}{Y : Set} where
    iso-is-fun : Coercion (X ≅ Y) (X → Y)
    iso-is-fun = record
      { coerce = _≅_.to }

    iso-is-iso : Coercion (X ≅ Y) (X ≅ Y)
    iso-is-iso = coerce-self _

    inj-is-fun : Coercion (X ↣ Y) (X → Y)
    inj-is-fun = record
      { coerce = proj₁ }

    srj-is-fun : Coercion (X ↠ Y) (X → Y)
    srj-is-fun = record
      { coerce = proj₁ }

    private
      module iso-methods {Source : Set}
                         ⦃ c : Coercion Source (X ≅ Y) ⦄ where
        private
          module with-source (source : Source) where
            private target = coerce c source
            open _≅_ target public using ()
              renaming (from to invert)
        open with-source public
    open iso-methods public

    iso⇒inj : (iso : X ≅ Y) → injective (apply iso)
    iso⇒inj f {x}{x'} q = (iso₁ x) ⁻¹ · ap from q · iso₁ x'
      where
        open _≅_ f

    iso⇒surj : (iso : X ≅ Y) → surjective (apply iso)
    iso⇒surj f y = from y , iso₂ y
      where
        open _≅_ f

    inj+surj⇒iso : (f : X → Y) → injective f → surjective f → X ≅ Y
    inj+surj⇒iso f inj-f surj-f = iso f g H K
      where
        g : Y → X
        g y = proj₁ (surj-f y)

        H : (x : X) → g (f x) ≡ x
        H x = inj-f (proj₂ (surj-f (f x)))

        K : (y : Y) → f (g y) ≡ y
        K y = proj₂ (surj-f y)

open properties public
