{-# OPTIONS --without-K #-}
module equality.calculus where

open import sum using (Σ ; _,_ ; proj₁; proj₂)
open import equality.core
open import equality.groupoid public
open import function.core

ap' : ∀ {i j} {X : Set i}{Y : X → Set j}
        {x x' : X}(f : (x : X) → Y x)(p : x ≡ x')
      → subst Y p (f x) ≡ f x'
ap' _ refl = refl

subst-naturality : ∀ {i i' j} {X : Set i} {Y : Set i'}
                   {x x' : X} (P : Y → Set j)
                   (f : X → Y)(p : x ≡ x')(u : P (f x))
                 → subst (P ∘ f) p u ≡ subst P (ap f p) u
subst-naturality _ _ refl _ = refl

subst-hom : ∀ {i j}{X : Set i}(P : X → Set j){x y z : X}
          → (p : x ≡ y)(q : y ≡ z)(u : P x)
          → subst P q (subst P p u) ≡ subst P (p · q) u
subst-hom _ refl q u = refl

subst-eq : ∀ {i} {X : Set i}{x y z : X}
         → (p : y ≡ x)(q : y ≡ z)
         → subst (λ y → y ≡ z) p q
         ≡ sym p · q
subst-eq refl _ = refl

subst-eq₂ : ∀ {i} {X : Set i}{x y : X}
          → (p : x ≡ y)
          → (q : x ≡ x)
          → subst (λ z → z ≡ z) p q ≡ sym p · q · p
subst-eq₂ refl q = sym (left-unit _)

subst-const : ∀ {i j} {A : Set i}{X : Set j}
            → {a a' : A}(p : a ≡ a')(x : X)
            → subst (λ _ → X) p x ≡ x
subst-const refl x = refl

subst-const-ap : ∀ {i j} {A : Set i}{X : Set j}
                 → {a a' : A}(f : A → X)(p : a ≡ a')
                 → ap' f p ≡ subst-const p (f a) · ap f p
subst-const-ap f refl = refl

apΣ : ∀ {i j}{A : Set i}{B : A → Set j}
        {x x' : Σ A B}
     → (p : x ≡ x')
     → Σ (proj₁ x ≡ proj₁ x') λ q
     → subst B q (proj₂ x) ≡ proj₂ x'
apΣ {B = B} p =
  J (λ x x' p → Σ (proj₁ x ≡ proj₁ x') λ q
              → subst B q (proj₂ x) ≡ proj₂ x')
    (λ x → refl , refl)
    _ _ p

unapΣ : ∀ {i j}{A : Set i}{B : A → Set j}
          {a a' : A}{b : B a}{b' : B a'}
        → (Σ (a ≡ a') λ q → subst B q b ≡ b')
        → (a , b) ≡ (a' , b')
unapΣ (refl , refl) = refl

pair≡ : ∀ {i j}{A : Set i}{B : Set j}
          {a a' : A}{b b' : B}
        → (a ≡ a') → (b ≡ b')
        → (a , b) ≡ (a' , b')
pair≡ refl refl = refl

apΣ-proj : ∀ {i j}{A : Set i}{B : A → Set j}
             {a a' : A}{b : B a}{b' : B a'}
             (p : (a , b) ≡ (a' , b'))
           → proj₁ (apΣ p)
           ≡ ap proj₁ p
apΣ-proj =
  J (λ _ _ p → proj₁ (apΣ p) ≡ ap proj₁ p)
    (λ x → refl) _ _

apΣ-sym : ∀ {i j}{A : Set i}{B : A → Set j}
            {a a' : A}{b : B a}{b' : B a'}
            (p : (a , b) ≡ (a' , b'))
          → proj₁ (apΣ (sym p))
          ≡ sym (proj₁ (apΣ p))
apΣ-sym =
  J (λ _ _ p → proj₁ (apΣ (sym p))
             ≡ sym (proj₁ (apΣ p)))
    (λ x → refl) _ _

subst-ap : ∀ {i j}{A : Set i}{B : Set j}{a a' : A}
           → (f : A → B)
           → (p : a ≡ a')
           → ap f (sym p)
           ≡ subst (λ x → f x ≡ f a) p refl
subst-ap f refl = refl

ap-map-id : ∀ {i j}{X : Set i}{Y : Set j}{x : X}
            → (f : X → Y)
            → ap f (refl {x = x}) ≡ refl {x = f x}
ap-map-id f = refl

ap-map-hom : ∀ {i j}{X : Set i}{Y : Set j}{x y z : X}
             → (f : X → Y)(p : x ≡ y)(q : y ≡ z)
             → ap f (p · q) ≡ ap f p · ap f q
ap-map-hom f refl _ = refl

ap-id : ∀ {l} {A : Set l}{x y : A}(p : x ≡ y)
        → ap id p ≡ p
ap-id refl = refl

ap-hom : ∀ {l m n} {A : Set l}{B : Set m}{C : Set n}
           {x y : A}(f : A → B)(g : B → C)(p : x ≡ y)
         → ap g (ap f p) ≡ ap (g ∘ f) p
ap-hom f g refl = refl

ap-inv : ∀ {i j} {X : Set i} {Y : Set j}
         → {x x' : X}
         → (f : X → Y)(p : x ≡ x')
         → ap f (sym p) ≡ sym (ap f p)
ap-inv f refl = refl

double-inverse : ∀ {i} {X : Set i} {x y : X}
               (p : x ≡ y) → sym (sym p) ≡ p
double-inverse refl = refl

inverse-comp : ∀ {i} {X : Set i} {x y z : X}
               (p : x ≡ y)(q : y ≡ z)
             → sym (p · q) ≡ sym q · sym p
inverse-comp refl q = sym (left-unit (sym q))

inverse-unique : ∀ {i} {X : Set i} {x y : X}
                 (p : x ≡ y)(q : y ≡ x)
               → p · q ≡ refl
               → sym p ≡ q
inverse-unique refl q t = sym t
