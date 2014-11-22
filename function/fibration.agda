{-# OPTIONS --without-K #-}

module function.fibration where

open import level
open import sum
open import equality.core
open import function.core
open import function.isomorphism.core
open import function.isomorphism.coherent
open import function.isomorphism.univalence
open import function.isomorphism.utils
open import function.extensionality.core
open import function.extensionality.proof
open import function.overloading
open import hott.level.core
open import hott.equivalence.core
open import hott.equivalence.alternative
open import hott.univalence
open import sets.unit

Fibration : ∀ {i} j → Set i → Set _
Fibration j X = Σ (Set j) λ Y → Y → X

fib : ∀ {i j}{X : Set i}(Y : X → Set j)
    → Σ X Y → X
fib Y = proj₁

fib-iso : ∀ {i j}{X : Set i}{Y : X → Set j}
        → (x : X)
        → fib Y ⁻¹ x ≅ Y x
fib-iso {X = X}{Y = Y} x = begin
    fib Y ⁻¹ x
  ≅⟨ refl≅ ⟩
    ( Σ (Σ X Y) λ { (x' , y)
    → x' ≡ x } )
  ≅⟨ Σ-assoc-iso ⟩
    ( Σ X λ x' → Y x' × x' ≡ x )
  ≅⟨ (Σ-ap-iso refl≅ λ x' → ×-comm) ⟩
    ( Σ X λ x' → x' ≡ x × Y x' )
  ≅⟨ sym≅ Σ-assoc-iso ⟩
    ( Σ (singleton' x) λ { (x' , _) → Y x' } )
  ≅⟨ Σ-ap-iso' (contr-⊤-iso (singl-contr' x)) (λ _ → refl≅) ⟩
    ( ⊤ × Y x )
  ≅⟨ ×-left-unit ⟩
    Y x
  ∎
  where open ≅-Reasoning

total-iso : ∀ {i j}{X : Set i}{Y : Set j}(p : Y → X)
          → (Σ X (_⁻¹_ p)) ≅ Y
total-iso {X = X}{Y = Y} p = begin
    ( Σ X λ x → (Σ Y λ y → p y ≡ x) )
  ≅⟨ Σ-comm-iso ⟩
    ( Σ Y λ y → (Σ X λ x → p y ≡ x) )
  ≅⟨ ( Σ-ap-iso refl≅ λ y → contr-⊤-iso (singl-contr (p y)) ) ⟩
    (Y × ⊤)
  ≅⟨ ×-right-unit ⟩
    Y
  ∎
  where open ≅-Reasoning

fib-eq-iso : ∀ {i j}{X : Set i}{Y₁ Y₂ : Set j}
           → (p₁ : Y₁ → X) (p₂ : Y₂ → X)
           → _≡_ {A = Fibration _ X} (Y₁ , p₁) (Y₂ , p₂)
           ≅ ( Σ (Y₁ ≅' Y₂) λ q → p₁ ≡ p₂ ∘ apply q )
fib-eq-iso {i}{j}{X}{Y₁}{Y₂} p₁ p₂ = begin
    _≡_ {A = Fibration _ X} (Y₁ , p₁) (Y₂ , p₂)
  ≅⟨ sym≅ Σ-split-iso ⟩
    ( Σ (Y₁ ≡ Y₂) λ q → subst (λ Y → Y → X) q p₁ ≡ p₂ )
  ≅⟨ ( Σ-ap-iso refl≅ λ q → lem q p₁ p₂ ) ⟩
    ( Σ (Y₁ ≡ Y₂) λ q → p₁ ≡ p₂ ∘ coerce q )
  ≅⟨ step ⟩
    ( Σ (Y₁ ≅' Y₂) λ q → p₁ ≡ p₂ ∘ apply q )
  ∎
  where
    open ≅-Reasoning
    abstract
      step : ( Σ (Y₁ ≡ Y₂) λ q → p₁ ≡ p₂ ∘ coerce q )
           ≅ ( Σ (Y₁ ≅' Y₂) λ q → p₁ ≡ p₂ ∘ apply q )
      step = Σ-ap-iso (uni-iso ·≅ ≈⇔≅') λ q → refl≅

    abstract
      lem : {Y₁ Y₂ : Set j}(q : Y₁ ≡ Y₂)(p₁ : Y₁ → X)(p₂ : Y₂ → X)
          → (subst (λ Y → Y → X) q p₁ ≡ p₂)
          ≅ (p₁ ≡ p₂ ∘ coerce q)
      lem refl p₁ p₂ = refl≅

fibration-iso : ∀ {i} j {X : Set i}
              → (Σ (Set (i ⊔ j)) λ Y → Y → X)
              ≅ (X → Set (i ⊔ j))
fibration-iso {i} j {X} = record
  { to = λ { (Y , p) x → p ⁻¹ x }
  ; from = λ P → (Σ X P , fib P)
  ; iso₁ = λ { (Y , p) → α Y p }
  ; iso₂ = λ P → funext λ x → ≅⇒≡ (fib-iso x) }
  where
    α : (Y : Set (i ⊔ j))(p : Y → X)
      → _≡_ {A = Σ (Set (i ⊔ j)) λ Y → Y → X}
        (Σ X (_⁻¹_ p) , proj₁)
        (Y , p)
    α Y p = invert (fib-eq-iso proj₁ p)
            ( ≅⇒≅' (total-iso p)
            , funext λ { (y , x , eq) → sym eq } )

fib-compose : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
            → (f : X → Y)(g : Y → Z)(z : Z)
            → (g ∘' f) ⁻¹ z
            ≅ ( Σ (g ⁻¹ z) λ { (y , _) → f ⁻¹ y } )
fib-compose {X = X}{Y}{Z} f g z = begin
    (g ∘' f) ⁻¹ z
  ≅⟨ refl≅ ⟩
    ( Σ X λ x → g (f x) ≡ z )
  ≅⟨ Σ-ap-iso refl≅ (λ _ → sym≅ ×-left-unit) ⟩
    ( Σ X λ x → ⊤ × g (f x) ≡ z)
  ≅⟨ ( Σ-ap-iso refl≅ λ x
      → Σ-ap-iso (sym≅ (contr-⊤-iso (singl-contr (f x))) ) λ _
      → refl≅ ) ⟩
    ( Σ X λ x → singleton (f x) × g (f x) ≡ z )
  ≅⟨ ( Σ-ap-iso refl≅ λ x → Σ-assoc-iso ) ⟩
    ( Σ X λ x → Σ Y λ y → (f x ≡ y) × (g (f x) ≡ z) )
  ≅⟨ ( Σ-ap-iso refl≅ λ x
       → Σ-ap-iso refl≅ λ y
       → Σ-ap-iso refl≅ λ p
       → ≡⇒≅ (ap (λ u → g u ≡ z) p) ) ⟩
    ( Σ X λ x → Σ Y λ y → (f x ≡ y) × (g y ≡ z) )
  ≅⟨ Σ-comm-iso ⟩
    ( Σ Y λ y → Σ X λ x → (f x ≡ y) × (g y ≡ z) )
  ≅⟨ ( Σ-ap-iso refl≅ λ y → sym≅ Σ-assoc-iso ) ⟩
    ( Σ Y λ y → (f ⁻¹ y) × (g y ≡ z) )
  ≅⟨ ( Σ-ap-iso refl≅ λ y → ×-comm ) ⟩
    ( Σ Y λ y →  (g y ≡ z) × (f ⁻¹ y) )
  ≅⟨ sym≅ Σ-assoc-iso ⟩
    ( Σ (g ⁻¹ z) λ { (y , _) → f ⁻¹ y } )
  ∎
  where open ≅-Reasoning
