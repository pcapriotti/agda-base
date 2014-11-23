{-# OPTIONS --without-K  #-}
module sets.fin.universe where

open import sum
open import decidable
open import equality.core
open import equality.calculus
open import equality.inspect
open import function.isomorphism
open import function.core
open import function.extensionality
open import function.fibration
open import function.overloading
open import sets.core
open import sets.properties
open import sets.nat.core
  hiding (_≟_)
open import sets.nat.ordering
  hiding (compare)
open import sets.fin.core
open import sets.fin.ordering
open import sets.fin.properties
open import sets.unit
open import sets.empty
open import sets.bool
open import sets.vec.dependent
open import hott.level.core
open import hott.level.closure
open import hott.level.sets

fin-struct-iso : ∀ {n} → Fin (suc n) ≅ (⊤ ⊎ Fin n)
fin-struct-iso = record
  { to = λ { zero → inj₁ tt; (suc i) → inj₂ i }
  ; from = [ (λ _ → zero) ,⊎ (suc) ]
  ; iso₁ = λ { zero → refl ; (suc i) → refl }
  ; iso₂ = λ { (inj₁ _) → refl; (inj₂ i) → refl } }

fin0-empty : ⊥ ≅ Fin 0
fin0-empty = sym≅ (empty-⊥-iso (λ ()))

fin1-unit : ⊤ ≅ Fin 1
fin1-unit = record
  { to = λ _ → zero
  ; from = λ { zero → tt ; (suc ()) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ { zero → refl ; (suc ()) } }

fin2-bool : Bool ≅ Fin 2
fin2-bool = record
  { to = λ b → if b then # 0 else # 1
  ; from = true ∷∷ false ∷∷ ⟦⟧
  ; iso₁ = λ { true → refl ; false → refl }
  ; iso₂ = refl ∷∷ refl ∷∷ ⟦⟧ }

fin-sum : ∀ {n m} → (Fin n ⊎ Fin m) ≅ Fin (n + m)
fin-sum {0} = record
  { to = λ { (inj₁ ()) ; (inj₂ j) → j }
  ; from = λ { j → inj₂ j }
  ; iso₁ = λ { (inj₁ ()); (inj₂ j) → refl }
  ; iso₂ = λ _ → refl }
fin-sum {suc n}{m} = begin
    (Fin (suc n) ⊎ Fin m)
  ≅⟨ ⊎-ap-iso fin-struct-iso refl≅ ⟩
    ((⊤ ⊎ Fin n) ⊎ Fin m)
  ≅⟨ ⊎-assoc-iso ⟩
    (⊤ ⊎ (Fin n ⊎ Fin m))
  ≅⟨ ⊎-ap-iso refl≅ fin-sum ⟩
    (⊤ ⊎ Fin (n + m))
  ≅⟨ sym≅ fin-struct-iso ⟩
    Fin (suc (n + m))
  ∎
  where open ≅-Reasoning

fin-prod : ∀ {n m} → (Fin n × Fin m) ≅ Fin (n * m)
fin-prod {0} = iso (λ { (() , _) }) (λ ()) (λ { (() , _) }) (λ ())
fin-prod {suc n}{m} = begin
    (Fin (suc n) × Fin m)
  ≅⟨ ×-ap-iso fin-struct-iso refl≅ ⟩
    ((⊤ ⊎ Fin n) × Fin m)
  ≅⟨ ⊎×-distr-iso ⟩
    ((⊤ × Fin m) ⊎ (Fin n × Fin m))
  ≅⟨ ⊎-ap-iso ×-left-unit fin-prod ⟩
    (Fin m ⊎ (Fin (n * m)))
  ≅⟨ fin-sum ⟩
    (Fin (m + (n * m)))
  ≡⟨ refl ⟩
    Fin (suc n * m)
  ∎
  where open ≅-Reasoning

fin-exp : ∀ {n m} → (Fin n → Fin m) ≅ Fin (m ^ n)
fin-exp {0} = record
  { to = λ f → zero
  ; from = (λ ()) ∷∷ ⟦⟧
  ; iso₁ = λ f → funext λ ()
  ; iso₂ = refl ∷∷ ⟦⟧ }
fin-exp {suc n}{m} = begin
    (Fin (suc n) → Fin m)
  ≅⟨ (Π-ap-iso fin-struct-iso λ _ → refl≅) ⟩
    ((⊤ ⊎ Fin n) → Fin m)
  ≅⟨ iso (λ f → f (inj₁ tt) , f ∘' inj₂)
         (λ { (i , _) (inj₁ _) → i
            ; (_ , g) (inj₂ i) → g i })
         (λ f → funext λ { (inj₁ tt) → refl
                          ; (inj₂ i) → refl })
         (λ { (i , g) → refl }) ⟩
    (Fin m × (Fin n → Fin m))
  ≅⟨ ×-ap-iso refl≅ fin-exp ⟩
    (Fin m × Fin (m ^ n))
  ≅⟨ fin-prod ⟩
    Fin (m ^ (suc n))
  ∎
  where open ≅-Reasoning

factorial : ℕ → ℕ
factorial 0 = 1
factorial (suc n) = suc n * factorial n

fin-inj-iso : ∀ {n} → (Fin n ≅ Fin n) ≅ (Fin n ↣ Fin n)
fin-inj-iso {n} = record
  { to = λ f → (apply f , iso⇒inj f)
  ; from = λ { (f , inj) → inj⇒iso f inj }
  ; iso₁ = λ f → iso-eq-h2 (fin-set n) (fin-set n) refl
  ; iso₂ = λ { (f , inj) → inj-eq-h2 (fin-set n) refl } }

fin-iso-iso : ∀ {n} → (Fin n ↣ Fin n) ≅ Fin (factorial n)
fin-iso-iso {0} = record
  { to = λ { (f , _) → zero }
  ; from = λ _ → (λ ()) , (λ { {()} p })
  ; iso₁ = λ { (f , _) → inj-eq-h2 (fin-set _) (funext λ ()) }
  ; iso₂ = λ { zero → refl ; (suc ()) } }
fin-iso-iso {suc n} = begin
    (X ↣ X)
  ≅⟨ sym≅ (total-iso classify) ⟩
    (Σ X λ i → classify ⁻¹ i)
  ≅⟨ (Σ-ap-iso₂ λ i → trans≅ (sym≅ (const-fibre i)) fibre-zero-iso) ⟩
    (Fin (suc n) × (Fin n ↣ Fin n))
  ≅⟨ ×-ap-iso refl≅ fin-iso-iso ⟩
    (Fin (suc n) × Fin (factorial n))
  ≅⟨ fin-prod ⟩
    Fin (factorial (suc n))
  ∎
  where
    X = Fin (suc n)
    open ≅-Reasoning

    classify : (X ↣ X) → X
    classify (f , _) = f zero

    const-fibre : (i : X) → classify ⁻¹ zero ≅ classify ⁻¹ i
    const-fibre i = begin
        ( Σ (X ↣ X) λ { (f , _) → f zero ≡ zero } )
      ≅⟨ ( Σ-ap-iso (transpose-inj-iso' zero i) (λ { (f , inj)
         → mk-prop-iso (fin-set _ _ _) (fin-set _ _ _)
                       (ap (transpose zero i)) (u f) }) ) ⟩
        ( Σ (X ↣ X) λ { (f , _) → f zero ≡ i } )
      ∎
      where
        u : (f : X → X)
          → transpose zero i (f zero) ≡ i
          → f zero ≡ zero
        u f p = sym (_≅_.iso₁ (transpose-iso zero i) (f zero))
              · (ap (transpose zero i) p
              · transpose-β₂ zero i)

    fibre-zero-iso : classify ⁻¹ zero ≅ (Fin n ↣ Fin n)
    fibre-zero-iso = record
      { to = λ { (f , z) → fin-inj-remove₀ f z }
      ; from = λ { g → fin-inj-add g , refl }
      ; iso₁ = λ { (f , p)
                 → unapΣ (inj-eq-h2 (fin-set (suc n))
                         (funext (α f p ))
                         , h1⇒prop (fin-set (suc n) _ _) _ _) }
      ; iso₂ = λ g → inj-eq-h2 (fin-set n) refl }
        where
            α : (f : Fin (suc n) ↣ Fin (suc n))
              → (p : apply f zero ≡ zero)
              → (i : Fin (suc n))
              → apply (fin-inj-add (fin-inj-remove₀ f p)) i
              ≡ apply f i
            α _ p zero = sym p
            α (f , f-inj) p (suc i) = pred-β (f (suc i))
              (λ q → fin-disj _ (f-inj (p · sym q)))

fin-subsets : ∀ {n} → (Fin n → Bool) ≅ Fin (2 ^ n)
fin-subsets = trans≅ (Π-ap-iso refl≅ λ _ → fin2-bool) fin-exp
