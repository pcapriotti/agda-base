{-# OPTIONS --without-K --type-in-type #-}

module function.isomorphism.utils where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.overloading
open import function.isomorphism.core
open import function.isomorphism.coherent
open import function.extensionality.proof
open import sets.unit
open import sets.empty
open import hott.hlevel.core

Σ-split-iso : {X : Set}{Y : X → Set}
            → {a a' : X}{b : Y a}{b' : Y a'}
            → (Σ (a ≡ a') λ q → subst Y q b ≡ b')
            ≅ ((a , b) ≡ (a' , b'))
Σ-split-iso {Y = Y}{a}{a'}{b}{b'} = iso unapΣ apΣ H K
  where
    H : ∀ {a a'}{b : Y a}{b' : Y a'}
      → (p : Σ (a ≡ a') λ q → subst Y q b ≡ b')
      → apΣ (unapΣ {a = a}{a' = a'}{b = b}{b' = b'} p) ≡ p
    H (refl , refl) = refl

    K : (p : (a , b) ≡ (a' , b')) → unapΣ (apΣ p) ≡ p
    K = J (λ u v p → unapΣ (apΣ p) ≡ p)
          (λ {(a , b) → refl })
          (a , b) (a' , b')

×-ap-iso : {X : Set}{X' : Set}
           {Y : Set}{Y' : Set}
         → (isom : X ≅ X')
         → (isom' : Y ≅ Y')
         → (X × Y) ≅ (X' × Y')
×-ap-iso isom isom' = record
  { to = λ { (x , y) → (apply isom x , apply isom' y) }
  ; from = λ { (x' , y') → (invert isom x' , invert isom' y') }
  ; iso₁ = λ { (x , y) → pair≡ (_≅_.iso₁ isom x) (_≅_.iso₁ isom' y) }
  ; iso₂ = λ { (x' , y') → pair≡ (_≅_.iso₂ isom x') (_≅_.iso₂ isom' y') } }

Σ-ap-iso₂ : {X : Set}{Y : X → Set}{Y' : X → Set}
          → ((x : X) → Y x ≅ Y' x)
          → Σ X Y ≅ Σ X Y'
Σ-ap-iso₂ {X = X}{Y}{Y'} isom = record
  { to = λ { (x , y) → (x , apply (isom x) y) }
  ; from = λ { (x , y') → (x , invert (isom x) y') }
  ; iso₁ = λ { (x , y) → unapΣ (refl , _≅_.iso₁ (isom x) y) }
  ; iso₂ = λ { (x , y') → unapΣ (refl , _≅_.iso₂ (isom x) y') } }

Σ-ap-iso₁ : {X : Set}{X' : Set}{Y : X' → Set}
          → (isom : X ≅ X')
          → Σ X (Y ∘ apply isom) ≅ Σ X' Y
Σ-ap-iso₁ {X = X}{X'}{Y} isom = record
  { to = λ { (x , y) → (f x , y) }
  ; from = λ { (x , y) → (g x , subst Y (sym (K x)) y) }
  ; iso₁ = λ { (x , y) → unapΣ (H x ,
           subst-naturality Y f (H x) _
         · (subst-hom Y (sym (K (f x))) (ap f (H x)) y
         · ap (λ p → subst Y p y) (lem x) ) ) }
  ; iso₂ = λ { (x , y) → unapΣ (K x ,
           subst-hom Y (sym (K x)) (K x) y
         · ap (λ p → subst Y p y) (right-inverse (K x)) ) } }
  where
    isom-c = ≅⇒≅' isom
    γ = proj₂ isom-c
    open _≅_ (proj₁ isom-c)
      renaming ( to to f ; from to g
               ; iso₁ to H; iso₂ to K )

    lem : (x : X) → sym (K (f x)) · ap f (H x) ≡ refl
    lem x = ap (λ z → sym (K (f x)) · z) (γ x)
          · right-inverse (K (f x))

Σ-ap-iso : {X : Set}{X' : Set}
           {Y : X → Set}{Y' : X' → Set}
         → (isom : X ≅ X')
         → ((x : X) → Y x ≅ Y' (apply isom x))
         → Σ X Y ≅ Σ X' Y'
Σ-ap-iso {X = X}{X'}{Y}{Y'} isom isom' = trans≅
  (Σ-ap-iso₂ isom') (Σ-ap-iso₁ isom)

Σ-ap-iso' : {X : Set}{X' : Set}
            {Y : X → Set}{Y' : X' → Set}
          → (isom : X ≅ X')
          → ((x : X') → Y (invert isom x) ≅ Y' x)
          → Σ X Y ≅ Σ X' Y'
Σ-ap-iso' {X = X}{X'}{Y}{Y'} isom isom'
  = sym≅ (Σ-ap-iso (sym≅ isom) (λ x → sym≅ (isom' x)))

Π-ap-iso : {X : Set}{X' : Set}
           {Y : X → Set}{Y' : X' → Set}
           → (isom : X ≅ X')
           → ((x' : X') → Y (invert isom x') ≅ Y' x')
           → ((x : X) → Y x)
           ≅ ((x' : X') → Y' x')
Π-ap-iso {X = X}{X'}{Y}{Y'} isom isom' =
  trans≅ (Π-iso (≅⇒≅' isom)) (Π-iso' isom')
  where
    Π-iso : (isom : X ≅' X')
          → ((x : X) → Y x)
          ≅ ((x' : X') → Y (invert (proj₁ isom) x'))
    Π-iso (iso f g H K , γ) = record
      { to = λ h x' → h (g x')
      ; from = λ h' x → subst Y (H x) (h' (f x))
      ; iso₁ = λ h → funext λ x → ap' h (H x)
      ; iso₂ = λ h' → funext λ x' →
              ap (λ p → subst Y p _) (sym (γ' x'))
            · sym (subst-naturality Y g (K x') _)
            · ap' h' (K x') }
      where γ' = co-coherence (iso f g H K) γ

    Π-iso' : {X : Set}{Y : X → Set}{Y' : X → Set}
           → ((x : X) → Y x ≅ Y' x)
           → ((x : X) → Y x)
           ≅ ((x : X) → Y' x)
    Π-iso' isom = record
      { to = λ h x → apply (isom x) (h x)
      ; from = λ h' x → invert (isom x) (h' x)
      ; iso₁ = λ h → funext λ x → _≅_.iso₁ (isom x) _
      ; iso₂ = λ h' → funext λ x → _≅_.iso₂ (isom x) _ }

ΠΣ-swap-iso : {X : Set}{Y : X → Set}
            → {Z : (x : X) → Y x → Set}
            → ((x : X) → Σ (Y x) λ y → Z x y)
            ≅ (Σ ((x : X) → Y x) λ f → ((x : X) → Z x (f x)))
ΠΣ-swap-iso = record
  { to = λ f → (proj₁ ∘' f , proj₂ ∘' f)
  ; from = λ { (f , g) x → (f x , g x) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

curry-iso : {X : Set}{Y : X → Set}
            (Z : (x : X) → Y x → Set)
          → ((xy : Σ X Y) → Z (proj₁ xy) (proj₂ xy))
          ≅ ((x : X) → (y : Y x) → Z x y)
curry-iso _ = record
  { to = λ f x y → f (x , y)
  ; from = λ { f (x , y) → f x y }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

Π-comm-iso : {X : Set}{Y : Set}{Z : X → Y → Set}
           → ((x : X)(y : Y) → Z x y)
           ≅ ((y : Y)(x : X) → Z x y)
Π-comm-iso = record
  { to = λ f y x → f x y
  ; from = λ f x y → f y x
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

Σ-comm-iso : {X : Set}{Y : Set}{Z : X → Y → Set}
           → (Σ X λ x → Σ Y λ y → Z x y)
           ≅ (Σ Y λ y → Σ X λ x → Z x y)
Σ-comm-iso = record
  { to = λ { (x , y , z) → (y , x , z) }
  ; from = λ { (y , x , z) → (x , y , z) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

impl-iso : {X : Set}{Y : X → Set}
         → ((x : X) → Y x) ≅ ({x : X} → Y x)
impl-iso = record
  { to = λ f → f _
  ; from = λ f _ → f
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

Σ-assoc-iso : {X : Set}{Y : X → Set}
              {Z : (x : X) → Y x → Set}
            → Σ (Σ X Y) (λ {(x , y) → Z x y})
            ≅ Σ X λ x → Σ (Y x) (Z x)
Σ-assoc-iso = record
  { to = λ {((x , y) , z) → (x , y , z) }
  ; from = λ {(x , y , z) → ((x , y) , z) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

⊎-ap-iso : {X : Set}{X' : Set}
         → {Y : Set}{Y' : Set}
         → X ≅ X'
         → Y ≅ Y'
         → (X ⊎ Y) ≅ (X' ⊎ Y')
⊎-ap-iso (iso f g α β) (iso f' g' α' β') = record
  { to = λ { (inj₁ x) → inj₁ (f x) ; (inj₂ y) → inj₂ (f' y) }
  ; from = λ { (inj₁ x) → inj₁ (g x) ; (inj₂ y) → inj₂ (g' y) }
  ; iso₁ = λ { (inj₁ x) → ap inj₁ (α x) ; (inj₂ y) → ap inj₂ (α' y) }
  ; iso₂ = λ { (inj₁ x) → ap inj₁ (β x) ; (inj₂ y) → ap inj₂ (β' y) } }

⊎-assoc-iso : {X : Set}{Y : Set}{Z : Set}
            → ((X ⊎ Y) ⊎ Z)
            ≅ (X ⊎ (Y ⊎ Z))
⊎-assoc-iso = record
  { to = λ { (inj₁ (inj₁ x)) → inj₁ x
           ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y)
           ; (inj₂ z) → inj₂ (inj₂ z) }
  ; from = λ { (inj₁ x) → inj₁ (inj₁ x)
             ; (inj₂ (inj₁ y)) → inj₁ (inj₂ y)
             ; (inj₂ (inj₂ z)) → inj₂ z }
  ; iso₁ = λ { (inj₁ (inj₁ x)) → refl
             ; (inj₁ (inj₂ y)) → refl
             ; (inj₂ z) → refl }
  ; iso₂ = λ { (inj₁ x) → refl
             ; (inj₂ (inj₁ y)) → refl
             ; (inj₂ (inj₂ z)) → refl } }

⊎×-distr-iso : {X : Set}{Y : Set}{Z : Set}
             → ((X ⊎ Y) × Z)
             ≅ ((X × Z) ⊎ (Y × Z))
⊎×-distr-iso = record
  { to = λ { (inj₁ x , z) → inj₁ (x , z)
           ; (inj₂ y , z) → inj₂ (y , z) }
  ; from = λ { (inj₁ (x , z)) → inj₁ x , z
             ; (inj₂ (y , z)) → inj₂ y , z }
  ; iso₁ = λ { (inj₁ x , z) → refl
             ; (inj₂ y , z) → refl }
  ; iso₂ = λ { (inj₁ (x , z)) → refl
             ; (inj₂ (y , z)) → refl } }

×-left-unit : {X : Set} → (⊤ × X) ≅ X
×-left-unit = record
  { to = λ {(tt , x) → x }
  ; from = λ x → tt , x
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

×-right-unit : {X : Set} → (X × ⊤) ≅ X
×-right-unit = record
  { to = λ {(x , tt) → x }
  ; from = λ x → x , tt
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

contr-⊤-iso : {X : Set}
            → contr X → X ≅ ⊤
contr-⊤-iso hX = record
  { to = λ x → tt
  ; from = λ { tt → proj₁ hX }
  ; iso₁ = λ x → proj₂ hX x
  ; iso₂ = λ { tt → refl } }

empty-⊥-iso : {X : Set} → (X → ⊥) → X ≅ ⊥
empty-⊥-iso u = record
  { to = u
  ; from = ⊥-elim
  ; iso₁ = λ x → ⊥-elim (u x)
  ; iso₂ = λ () }

×-comm : {X : Set}{Y : Set}
       → (X × Y) ≅ (Y × X)
×-comm = record
  { to = λ {(x , y) → (y , x)}
  ; from = λ {(y , x) → (x , y)}
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

Π-left-unit : {X : Set}
            → (⊤ → X) ≅ X
Π-left-unit = record
  { to = λ f → f tt
  ; from = λ x _ → x
  ; iso₁ = λ _ → refl
  ; iso₂ = λ f → refl }

total-space-iso : {A : Set}{B : Set}
                → (f : A → B)
                → (Σ B λ b → f ⁻¹ b) ≅ A
total-space-iso {A = A}{B} f = begin
    (Σ B λ b → Σ A λ a → f a ≡ b)
  ≅⟨ Σ-comm-iso ⟩
    (Σ A λ a → singleton (f a))
  ≅⟨ Σ-ap-iso₂ (λ a → contr-⊤-iso (singl-contr (f a))) ⟩
    (A × ⊤)
  ≅⟨ ×-right-unit ⟩
    A
  ∎
  where open ≅-Reasoning

-- rewriting lemmas for equations on equalities
sym≡-iso : {X : Set}(x y : X)
         → (x ≡ y)
         ≅ (y ≡ x)
sym≡-iso _ _ = iso sym sym double-inverse double-inverse

trans≡-iso : {X : Set}{x y z : X}
           → (x ≡ y)
           → (y ≡ z) ≅ (x ≡ z)
trans≡-iso p = record
  { to = λ q → p · q
  ; from = λ q → sym p · q
  ; iso₁ = λ q → sym (associativity (sym p) p q)
                · ap (λ z → z · q) (right-inverse p)
  ; iso₂ = λ q → sym (associativity p (sym p) q)
                · ap (λ z → z · q) (left-inverse p) }

trans≡-iso' : {X : Set}{x y z : X}
            → (y ≡ z)
            → (x ≡ y) ≅ (x ≡ z)
trans≡-iso' q = record
  { to = λ p → p · q
  ; from = λ p → p · sym q
  ; iso₁ = λ p → associativity p q (sym q)
               · ap (_·_ p) (left-inverse q)
               · left-unit p
  ; iso₂ = λ p → associativity p (sym q) q
               · (ap (_·_ p) (right-inverse q)
               · left-unit p) }

move-≡-iso : {X : Set}{x y z : X}
           → (p : x ≡ y)(q : y ≡ z)(r : x ≡ z)
           → (p · q ≡ r)
           ≅ (sym p · r ≡ q)
move-≡-iso refl = sym≡-iso

J-iso : {X : Set}{x : X}
      → {P : (y : X) → x ≡ y → Set}
      → P x refl
      ≅ ((y : X)(p : x ≡ y) → P y p)
J-iso {X = X}{x}{P} = record
  { to = J' P
  ; from = λ u → u x refl
  ; iso₁ = λ _ → refl
  ; iso₂ = λ u → funext λ y → funext λ p → β u y p }
  where
    β : (u : (y : X)(p : x ≡ y) → P y p)
      → (y : X)(p : x ≡ y)
      → J' P (u x refl) y p ≡ u y p
    β u .x refl = refl
