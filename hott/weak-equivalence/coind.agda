{-# OPTIONS --without-K #-}
module hott.weak-equivalence.coind where

open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.extensionality
open import function.isomorphism
open import container.core
open import container.fixpoint
open import container.m
open import hott.weak-equivalence.core
open import hott.weak-equivalence.alternative
open import hott.hlevel
open import sets.unit

apply≅' : ∀ {i j}{X : Set i}{Y : Set j}
        → X ≅' Y → X → Y
apply≅' (i , _) = _≅_.to i

is-≅' : ∀ {i j}{X : Set i}{Y : Set j} → (X → Y) → Set _
is-≅' {X = X}{Y = Y} f = Σ (X ≅' Y) λ isom → f ≡ apply isom

abstract
  is-≅'-≈-iso : ∀ {i j}{X : Set i}{Y : Set j}(f : X → Y)
              → is-≅' f ≅ weak-equiv f
  is-≅'-≈-iso {X = X}{Y = Y} f = begin
      (Σ (X ≅' Y) λ isom → f ≡ apply isom)
    ≅⟨ Σ-ap-iso (sym≅ ≈⇔≅') (λ _ → refl≅) ⟩
      (Σ (Σ (X → Y) λ f' → weak-equiv f') λ eq → f ≡ proj₁ eq)
    ≅⟨ Σ-assoc-iso ⟩
      (Σ (X → Y) λ f' → (weak-equiv f' × f ≡ f'))
    ≅⟨ (Σ-ap-iso refl≅ λ f' → ×-comm) ⟩
      (Σ (X → Y) λ f' → (f ≡ f' × weak-equiv f'))
    ≅⟨ sym≅ Σ-assoc-iso ⟩
      (Σ (Σ (X → Y) λ f' → f ≡ f') λ {(f' , _) → weak-equiv f'})
    ≅⟨ Σ-ap-iso (contr-⊤-iso (singl-contr f)) (λ _ → refl≅) ⟩
      (⊤ × weak-equiv f)
    ≅⟨ ×-left-unit ⟩
      weak-equiv f
    ∎
    where open ≅-Reasoning

is-≅'-h1 : ∀ {i j}{X : Set i}{Y : Set j}
         → (f : X → Y) → h 1 (is-≅' f)
is-≅'-h1 f = iso-hlevel (sym≅ (is-≅'-≈-iso f)) (weak-equiv-h1 f)

≅'-Σ-iso : ∀ {i j}{X : Set i}{Y : Set j}
         → (X ≅' Y) ≅ (Σ (X → Y) λ f → is-≅' f)
≅'-Σ-iso {X = X}{Y = Y} = begin
    (X ≅' Y)
  ≅⟨ sym≅ ×-right-unit ⟩
    ((X ≅' Y) × ⊤)
  ≅⟨ sym≅ (Σ-ap-iso refl≅ λ i → contr-⊤-iso (singl-contr (apply i))) ⟩
    (Σ (X ≅' Y) λ i → singleton (apply i))
  ≅⟨ ( Σ-ap-iso refl≅ λ i → Σ-ap-iso refl≅ λ f → sym≡-iso (apply i) f ) ⟩
    (Σ (X ≅' Y) λ i → Σ (X → Y) λ f → f ≡ apply i)
  ≅⟨ sym≅ Σ-assoc-iso ⟩
    (Σ ((X ≅' Y) × (X → Y)) λ {(i , f) → f ≡ apply i})
  ≅⟨ Σ-ap-iso ×-comm (λ _ → refl≅) ⟩
    (Σ ((X → Y) × (X ≅' Y)) λ {(f , i) → f ≡ apply i})
  ≅⟨ Σ-assoc-iso ⟩
    (Σ (X → Y) λ f → Σ (X ≅' Y) λ i → f ≡ apply i)
  ∎
  where open ≅-Reasoning

≅'-equality : ∀ {i j}{X : Set i}{Y : Set j}
            → {isom₁ isom₂ : X ≅' Y}
            → (apply isom₁ ≡ apply isom₂)
            → isom₁ ≡ isom₂
≅'-equality {X = X}{Y = Y} {isom₁}{isom₂} p = iso⇒inj ≅'-Σ-iso q
  where
    q : apply ≅'-Σ-iso isom₁ ≡ apply ≅'-Σ-iso isom₂
    q = unapΣ (p , h1⇒prop (is-≅'-h1 _) _ _)

record F {i j}(Z : ∀ {i j} → Set i → Set j → Set (i ⊔ j))
         (X : Set i)(Y : Set j) : Set (i ⊔ j) where
  constructor mk-F
  field
    f : X → Y
    g : Y → X
    φ : (x : X)(y : Y) → Z (f x ≡ y) (x ≡ g y)

~-container : ∀ i → Container _ _ _
~-container i = record
  { I = Set i × Set i
  ; A = λ { (X , Y) → (X → Y) × (Y → X) }
  ; B = λ { {X , Y} _ → X × Y }
  ; r = λ { {a = f , g} (x , y) → (f x ≡ y) , (x ≡ g y) } }

module D {i} where
  open Definition (~-container i) public
  open Fixpoint (fix M fixpoint) public
    hiding (fixpoint)

unfold≅' : ∀ {i}{X Y : Set i}
         → X ≅' Y → D.F (λ { (X , Y) → X ≅' Y }) (X , Y)
unfold≅' {X = X}{Y = Y} (iso f g α β , δ) =
    ((f , g) , λ {(x , y) → ≅⇒≅' (φ x y)})
  where
    open ≡-Reasoning

    δ' = co-coherence (iso f g α β) δ

    iso₁ : {x : X}{y : Y}(p : f x ≡ y)
         → ap f (sym (α x) · ap g p) · β y ≡ p
    iso₁ {x} .{f x} refl = begin
        ap f (sym (α x) · refl) · β (f x)
      ≡⟨ ap (λ z → ap f z · β (f x)) (left-unit (sym (α x)))  ⟩
        ap f (sym (α x)) · β (f x)
      ≡⟨ ap (λ z → z · β (f x)) (ap-inv f (α x)) ⟩
        sym (ap f (α x)) · β (f x)
      ≡⟨ ap (λ z → sym z · β (f x)) (δ x) ⟩
        sym (β (f x)) · β (f x)
      ≡⟨ right-inverse (β (f x)) ⟩
        refl
      ∎

    iso₂' : {x : X}{y : Y}(q : g y ≡ x)
         → sym (α x) · ap g (ap f (sym q) · β y) ≡ sym q
    iso₂' .{g y}{y} refl = begin
        sym (α (g y)) · ap g (refl · β y)
      ≡⟨ ap (λ z → sym (α (g y)) · ap g z) (right-unit (β y)) ⟩
        sym (α (g y)) · ap g (β y)
      ≡⟨ ap (λ z → sym (α (g y)) · z) (δ' y) ⟩
        sym (α (g y)) · α (g y)
      ≡⟨ right-inverse (α (g y)) ⟩
        refl
      ∎

    iso₂ : {x : X}{y : Y}(q : x ≡ g y)
         → sym (α x) · ap g (ap f q · β y) ≡ q
    iso₂ {x}{y} q =
      subst (λ z → sym (α x) · ap g (ap f z · β y) ≡ z)
            (double-inverse q)
            (iso₂' (sym q))

    φ : (x : X)(y : Y) → (f x ≡ y) ≅ (x ≡ g y)
    φ x y = record
      { to = λ p → sym (α x) · ap g p
      ; from = λ q → ap f q · β y
      ; iso₁ = iso₁
      ; iso₂ = iso₂ }

Iso' : ∀ {i} → Set i × Set i → Set _
Iso' (X , Y) = X ≅' Y

_~_ : ∀ {i} → Set i → Set i → Set i
_~_ {i} X Y = D.M (X , Y)

apply~ : ∀ {i}{X Y : Set i} → X ~ Y → X → Y
apply~ eq = proj₁ (D.head eq)

invert~ : ∀ {i}{X Y : Set i} → X ~ Y → Y → X
invert~ eq = proj₂ (D.head eq)

private
  u : ∀ {i}{X Y : Set i} → X ~ Y → X ≅' Y
  u {X = X}{Y = Y} eq = ≅⇒≅' (iso f g α β)
    where
      f : X → Y
      f = apply~ eq

      g : Y → X
      g = invert~ eq

      φ : (x : X)(y : Y) → (f x ≡ y) ~ (x ≡ g y)
      φ x y = D.tail eq (x , y)

      α : (x : X) → g (f x) ≡ x
      α x = sym (apply~ (φ x (f x)) refl)

      β : (y : Y) → f (g y) ≡ y
      β y = invert~ (φ (g y) y) refl

  u-morphism : ∀ {i}{X Y : Set i}
             → (eq : X ~ Y)
             → unfold≅' (u eq)
             ≡ D.imap D.M u (D.out eq)
  u-morphism {i}{X}{Y} eq = unapΣ (refl , funext λ {(x , y) → lem₂ x y})
    where
      f : X → Y
      f = apply~ eq

      g : Y → X
      g = invert~ eq

      φ : (x : X)(y : Y) → (f x ≡ y) ~ (x ≡ g y)
      φ x y = D.tail eq (x , y)

      σ τ : (x : X)(y : Y) → (f x ≡ y) ≅' (x ≡ g y)
      σ x y = proj₂ (unfold≅' (u eq)) (x , y)
      τ x y = u (φ x y)

      lem : (x : X)(y : Y)(p : f x ≡ y)
           → apply≅' (σ x y) p ≡ apply≅' (τ x y) p
      lem x .(f x) refl = left-unit _ · double-inverse _

      lem₂ : (x : X)(y : Y) → proj₂ (unfold≅' (u eq)) (x , y)
                            ≡ u (D.tail eq (x , y))
      lem₂ x y = ≅'-equality (funext (lem x y))

  v : ∀ {i}{X Y : Set i} → X ≅' Y → X ~ Y
  v = D.unfold unfold≅'

  vu-morphism : ∀ {i}{X Y : Set i}
              → (eq : X ~ Y)
              → D.out (v (u eq))
              ≡ D.imap D.M (v ∘ u) (D.out eq)
  vu-morphism {X = X}{Y = Y} eq = ap (D.imap Iso' v) (u-morphism eq)

  vu-id : ∀ {i}{X Y : Set i} (eq : X ~ Y) → v (u eq) ≡ eq
  vu-id eq = D.unfold-η D.out (v ∘ u) vu-morphism eq · D.unfold-id eq

  uv-id : ∀ {i}{X Y : Set i} (i : X ≅' Y) → u (v i) ≡ i
  uv-id {X = X}{Y = Y} i = ≅'-equality refl

~⇔≅' : ∀ {i}{X Y : Set i} → (X ~ Y) ≅ (X ≅' Y)
~⇔≅' = iso u v vu-id uv-id
