{-# OPTIONS --without-K #-}
module equality.calculus where

open import sum using (Σ ; _,_ ; proj₁)
open import equality.core
  using (_≡_ ; refl ; sym ; subst ; cong)
open import category.instances.discrete
import category.groupoid.properties as GP
open import function using (id ; _∘_)

open DiscreteGroupoid public hiding (id ; _∘_)

section-naturality : ∀ {i} {X : Set i}{Y : X → Set i}
                 {x x' : X}(f : (x : X) → Y x)(p : x ≡ x')
               → subst Y p (f x) ≡ f x'
section-naturality _ refl = refl

subst-naturality : ∀ {i j} {X Y : Set i}{x x' : X} (P : Y → Set j)
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

congΣ : ∀ {i j}{A : Set i}{B : A → Set j}
        {a a' : A}{b : B a}{b' : B a'}
     → (p : (a , b) ≡ (a' , b'))
     → Σ (a ≡ a') λ q
     → subst B q b ≡ b'
congΣ refl = refl , refl

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
congΣ-proj refl = refl

congΣ-sym : ∀ {i j}{A : Set i}{B : A → Set j}
            {a a' : A}{b : B a}{b' : B a'}
            (p : (a , b) ≡ (a' , b'))
          → proj₁ (congΣ (sym p))
          ≡ sym (proj₁ (congΣ p))
congΣ-sym refl = refl

subst-cong : ∀ {i}{A B : Set i}{a a' : A}
           → (f : A → B)
           → (p : a ≡ a')
           → cong f (sym p)
           ≡ subst (λ x → f x ≡ f a) p refl
subst-cong f refl = refl

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
cong-inv {X = X} {Y = Y} f =
  GP.map-inv {G = discrete X} {H = discrete Y} (discrete-map f)

double-inverse : ∀ {i} {X : Set i} {x y : X}
               (p : x ≡ y) → sym (sym p) ≡ p
double-inverse = GP.double-inverse (discrete _)

inverse-comp : ∀ {i} {X : Set i} {x y z : X}
               (p : x ≡ y)(q : y ≡ z)
             → sym (p ⊚ q) ≡ sym q ⊚ sym p
inverse-comp = GP.inverse-comp (discrete _)