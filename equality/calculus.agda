{-# OPTIONS --without-K #-}
module equality.calculus where

open import sum using (Σ ; _,_ ; proj₁; proj₂)
open import equality.core
open import equality.groupoid public
open import function using (id ; _∘_)

cong' : ∀ {i j} {X : Set i}{Y : X → Set j}
        {x x' : X}(f : (x : X) → Y x)(p : x ≡ x')
      → subst Y p (f x) ≡ f x'
cong' _ refl = refl

subst-naturality : ∀ {i j} {X : Set i} {Y : Set j}
                   {x x' : X} (P : Y → Set j)
                   (f : X → Y)(p : x ≡ x')(u : P (f x))
                 → subst (P ∘ f) p u ≡ subst P (cong f p) u
subst-naturality _ _ refl _ = refl

subst-eq : ∀ {i} {X : Set i}{x y z : X}
         → (p : y ≡ x)(q : y ≡ z)
         → subst (λ y → y ≡ z) p q
         ≡ sym p ⊚ q
subst-eq refl _ = refl

subst-eq₂ : ∀ {i} {X : Set i}{x y : X}
          → (p : x ≡ y)
          → (q : x ≡ x)
          → subst (λ z → z ≡ z) p q ≡ sym p ⊚ q ⊚ p
subst-eq₂ refl q = sym (left-unit _)

subst-const : ∀ {i j} {A : Set i}{X : Set j}
            → {a a' : A}(p : a ≡ a')(x : X)
            → subst (λ _ → X) p x ≡ x
subst-const refl x = refl

subst-const-cong : ∀ {i j} {A : Set i}{X : Set j}
                 → {a a' : A}(f : A → X)(p : a ≡ a')
                 → cong' f p ≡ subst-const p (f a) ⊚ cong f p
subst-const-cong f refl = refl

congΣ : ∀ {i j}{A : Set i}{B : A → Set j}
        {x x' : Σ A B}
     → (p : x ≡ x')
     → Σ (proj₁ x ≡ proj₁ x') λ q
     → subst B q (proj₂ x) ≡ proj₂ x'
congΣ {B = B} p =
  J (λ x x' p → Σ (proj₁ x ≡ proj₁ x') λ q
              → subst B q (proj₂ x) ≡ proj₂ x')
    (λ x → refl , refl)
    _ _ p

uncongΣ : ∀ {i j}{A : Set i}{B : A → Set j}
          {a a' : A}{b : B a}{b' : B a'}
        → (Σ (a ≡ a') λ q → subst B q b ≡ b')
        → (a , b) ≡ (a' , b')
uncongΣ (refl , refl) = refl

congΣ-proj : ∀ {i j}{A : Set i}{B : A → Set j}
             {a a' : A}{b : B a}{b' : B a'}
             (p : (a , b) ≡ (a' , b'))
           → proj₁ (congΣ p)
           ≡ cong proj₁ p
congΣ-proj =
  J (λ _ _ p → proj₁ (congΣ p) ≡ cong proj₁ p)
    (λ x → refl) _ _

congΣ-sym : ∀ {i j}{A : Set i}{B : A → Set j}
            {a a' : A}{b : B a}{b' : B a'}
            (p : (a , b) ≡ (a' , b'))
          → proj₁ (congΣ (sym p))
          ≡ sym (proj₁ (congΣ p))
congΣ-sym =
  J (λ _ _ p → proj₁ (congΣ (sym p))
             ≡ sym (proj₁ (congΣ p)))
    (λ x → refl) _ _

subst-cong : ∀ {i j}{A : Set i}{B : Set j}{a a' : A}
           → (f : A → B)
           → (p : a ≡ a')
           → cong f (sym p)
           ≡ subst (λ x → f x ≡ f a) p refl
subst-cong f refl = refl

cong-map-id : ∀ {i j}{X : Set i}{Y : Set j}{x : X}
            → (f : X → Y)
            → cong f (refl {x = x}) ≡ refl {x = f x}
cong-map-id f = refl

cong-map-hom : ∀ {i j}{X : Set i}{Y : Set j}{x y z : X}
             → (f : X → Y)(p : x ≡ y)(q : y ≡ z)
             → cong f (p ⊚ q) ≡ cong f p ⊚ cong f q
cong-map-hom f refl _ = refl

cong-id : ∀ {l} {A : Set l}{x y : A}(p : x ≡ y)
        → cong id p ≡ p
cong-id refl = refl

cong-hom : ∀ {l m n} {A : Set l}{B : Set m}{C : Set n}
           {x y : A}(f : A → B)(g : B → C)(p : x ≡ y)
         → cong g (cong f p) ≡ cong (g ∘ f) p
cong-hom f g refl = refl

cong-inv : ∀ {i j} {X : Set i} {Y : Set j}
         → {x x' : X}
         → (f : X → Y)(p : x ≡ x')
         → cong f (sym p) ≡ sym (cong f p)
cong-inv f refl = refl

double-inverse : ∀ {i} {X : Set i} {x y : X}
               (p : x ≡ y) → sym (sym p) ≡ p
double-inverse refl = refl

inverse-comp : ∀ {i} {X : Set i} {x y z : X}
               (p : x ≡ y)(q : y ≡ z)
             → sym (p ⊚ q) ≡ sym q ⊚ sym p
inverse-comp refl q = sym (left-unit (sym q))

inverse-unique : ∀ {i} {X : Set i} {x y : X}
                 (p : x ≡ y)(q : y ≡ x)
               → p ⊚ q ≡ refl
               → sym p ≡ q
inverse-unique refl q t = sym t