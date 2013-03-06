{-# OPTIONS --without-K #-}

module function.isomorphism.utils where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism.core
open import function.isomorphism.coherent
open import function.extensionality.core
open import sets.unit
open import hott.hlevel.core

Σ-split-iso : ∀ {i j}{X : Set i}{Y : X → Set j}
            → {a a' : X}{b : Y a}{b' : Y a'}
            → (Σ (a ≡ a') λ q → subst Y q b ≡ b')
            ≅ ((a , b) ≡ (a' , b'))
Σ-split-iso {Y = Y}{a}{a'}{b}{b'} = iso uncongΣ congΣ H K
  where
    H : ∀ {a a'}{b : Y a}{b' : Y a'}
      → (p : Σ (a ≡ a') λ q → subst Y q b ≡ b')
      → congΣ (uncongΣ {a = a}{a' = a'}{b = b}{b' = b'} p) ≡ p
    H (refl , refl) = refl

    K : (p : (a , b) ≡ (a' , b')) → uncongΣ (congΣ p) ≡ p
    K = J (λ u v p → uncongΣ (congΣ p) ≡ p)
          (λ {(a , b) → refl })
          (a , b) (a' , b')

Σ-cong-iso : ∀ {i i' j j'}{X : Set i}{X' : Set i'}
             {Y : X → Set j}{Y' : X' → Set j'}
           → (isom : X ≅ X')
           → ((x' : X') → Y (invert isom x') ≅ Y' x')
           → Σ X Y ≅ Σ X' Y'
Σ-cong-iso {X = X}{X'}{Y}{Y'} isom isom' = trans≅ Σ-iso (Σ-iso' isom')
  where
    isom-c = ≅⇒≅' isom
    γ = proj₂ isom-c
    open _≅_ (proj₁ isom-c)
      renaming ( to to f ; from to g
               ; iso₁ to H; iso₂ to K )

    lem : (x : X') → sym (H (g x)) ⊚ cong g (K x) ≡ refl
    lem x = cong (λ z → sym (H (g x)) ⊚ z) (co-coherence _ γ x)
          ⊚ right-inverse (H (g x))

    Σ-iso : Σ X Y ≅ Σ X' (Y ∘ g)
    Σ-iso = record
      { to = λ { (x , y) → (f x , subst Y (sym (H x)) y) }
      ; from = λ { (x , y) → (g x , y) }
      ; iso₁ = λ { (x , y) → uncongΣ (H x ,
            subst-hom Y (sym (H x)) (H x) y
          ⊚ cong (λ p → subst Y p y) (right-inverse (H x)) ) }
      ; iso₂ = λ { (x , y) → uncongΣ (K x ,
            subst-naturality Y g (K x) _
          ⊚ (subst-hom Y (sym (H (g x))) (cong g (K x)) y
          ⊚ cong (λ p → subst Y p y) (lem x) ) ) } }

    Σ-iso' : ∀ {i j j'}{X : Set i}{Y : X → Set j}{Y' : X → Set j'}
           → ((x : X) → Y x ≅ Y' x)
           → Σ X Y ≅ Σ X Y'
    Σ-iso' isom = record
      { to = λ { (x , y) → (x , apply (isom x) y) }
      ; from = λ { (x , y') → (x , invert (isom x) y') }
      ; iso₁ = λ { (x , y) → uncongΣ (refl , _≅_.iso₁ (isom x) y) }
      ; iso₂ = λ { (x , y') → uncongΣ (refl , _≅_.iso₂ (isom x) y') } }

Π-cong-iso : ∀ {i i' j j'}{X : Set i}{X' : Set i'}
             {Y : X → Set j}{Y' : X' → Set j'}
           → (ext' : ∀ {i j} → Extensionality' i j)
           → (isom : X ≅ X')
           → ((x' : X') → Y (invert isom x') ≅ Y' x')
           → ((x : X) → Y x)
           ≅ ((x' : X') → Y' x')
Π-cong-iso {X = X}{X'}{Y}{Y'} ext' isom isom' =
  trans≅ (Π-iso (≅⇒≅' isom)) (Π-iso' isom')
  where
    Π-iso : (isom : X ≅' X')
          → ((x : X) → Y x)
          ≅ ((x' : X') → Y (invert (proj₁ isom) x'))
    Π-iso (iso f g H K , γ) = record
      { to = λ h x' → h (g x')
      ; from = λ h' x → subst Y (H x) (h' (f x))
      ; iso₁ = λ h → ext' λ x → cong' h (H x)
      ; iso₂ = λ h' → ext' λ x' →
              cong (λ p → subst Y p _) (sym (γ' x'))
            ⊚ sym (subst-naturality Y g (K x') _)
            ⊚ cong' h' (K x') }
      where γ' = co-coherence (iso f g H K) γ

    Π-iso' : ∀ {i j j'}{X : Set i}
             {Y : X → Set j}{Y' : X → Set j'}
           → ((x : X) → Y x ≅ Y' x)
           → ((x : X) → Y x)
           ≅ ((x : X) → Y' x)
    Π-iso' isom = record
      { to = λ h x → apply (isom x) (h x)
      ; from = λ h' x → invert (isom x) (h' x)
      ; iso₁ = λ h → ext' λ x → _≅_.iso₁ (isom x) _
      ; iso₂ = λ h' → ext' λ x → _≅_.iso₂ (isom x) _ }

ΠΣ-swap-iso : ∀ {i j k}{X : Set i}{Y : X → Set j}
            → {Z : (x : X) → Y x → Set k}
            → ((x : X) → Σ (Y x) λ y → Z x y)
            ≅ (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap-iso = record
  { to = λ f → (proj₁ ∘' f , proj₂ ∘' f)
  ; from = λ { (f , g) x → (f x , g x) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

curry-iso : ∀ {i j k}{X : Set i}{Y : X → Set j}
            (Z : (x : X) → Y x → Set k)
          → ((xy : Σ X Y) → Z (proj₁ xy) (proj₂ xy))
          ≅ ((x : X) → (y : Y x) → Z x y)
curry-iso _ = record
  { to = λ f x y → f (x , y)
  ; from = λ { f (x , y) → f x y }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

impl-iso : ∀ {i j}{X : Set i}{Y : X → Set j}
         → ((x : X) → Y x) ≅ ({x : X} → Y x)
impl-iso = record
  { to = λ f → f _
  ; from = λ f _ → f
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

Σ-assoc-iso : ∀ {i j k}
              {X : Set i}{Y : X → Set j}
              {Z : (x : X) → Y x → Set k}
            → Σ (Σ X Y) (λ {(x , y) → Z x y})
            ≅ Σ X λ x → Σ (Y x) (Z x)
Σ-assoc-iso = record
  { to = λ {((x , y) , z) → (x , y , z) }
  ; from = λ {(x , y , z) → ((x , y) , z) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

×-left-unit : ∀ {i}{X : Set i} → (⊤ × X) ≅ X
×-left-unit = record
  { to = λ {(tt , x) → x }
  ; from = λ x → tt , x
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

×-right-unit : ∀ {i}{X : Set i} → (X × ⊤) ≅ X
×-right-unit = record
  { to = λ {(x , tt) → x }
  ; from = λ x → x , tt
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

contr-⊤-iso : ∀ {i}{X : Set i}
            → contr X → X ≅ ⊤
contr-⊤-iso hX = record
  { to = λ x → tt
  ; from = λ { tt → proj₁ hX }
  ; iso₁ = λ x → proj₂ hX x
  ; iso₂ = λ { tt → refl } }

×-comm : ∀ {i j}{X : Set i}{Y : Set j}
       → (X × Y) ≅ (Y × X)
×-comm = record
  { to = λ {(x , y) → (y , x)}
  ; from = λ {(y , x) → (x , y)}
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

Π-left-unit : ∀ {i}{X : Set i}
            → (⊤ → X) ≅ X
Π-left-unit = record
  { to = λ f → f tt
  ; from = λ x _ → x
  ; iso₁ = λ _ → refl
  ; iso₂ = λ f → refl }

-- rewriting lemmas for equations on equalities
sym≡-iso : ∀ {i}{X : Set i}(x y : X)
         → (x ≡ y)
         ≅ (y ≡ x)
sym≡-iso _ _ = iso sym sym double-inverse double-inverse

move-≡-iso : ∀ {i}{X : Set i}{x y z : X}
           → (p : x ≡ y)(q : y ≡ z)(r : x ≡ z)
           → (p ⊚ q ≡ r)
           ≅ (sym p ⊚ r ≡ q)
move-≡-iso refl = sym≡-iso
