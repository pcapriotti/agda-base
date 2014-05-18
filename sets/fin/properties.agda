{-# OPTIONS --without-K  #-}
module sets.fin.properties where

open import sum
open import decidable
open import equality
open import function.core
open import function.extensionality
open import function.isomorphism
open import function.overloading
open import sets.core
open import sets.nat.core
  hiding (_≟_; pred)
open import sets.nat.ordering
open import sets.fin.core
open import sets.empty
open import sets.properties
open import hott.level.core
open import hott.level.closure
open import hott.level.sets

pred : ∀ {n}(i : Fin (suc n))
     → ¬ (i ≡ zero) → Fin n
pred zero u = ⊥-elim (u refl)
pred (suc j) _ = j

pred-β : ∀ {n}(i : Fin (suc n))
       → (u : ¬ (i ≡ zero))
       → suc (pred i u) ≡ i
pred-β zero u = ⊥-elim (u refl)
pred-β (suc i) u = refl

pred-inj : ∀ {n}{i j : Fin (suc n)}
         → (u : ¬ (i ≡ zero))
         → (v : ¬ (j ≡ zero))
         → pred i u ≡ pred j v
         → i ≡ j
pred-inj {n} {zero} u v p = ⊥-elim (u refl)
pred-inj {n} {suc i} {zero} u v p = ⊥-elim (v refl)
pred-inj {n} {suc i} {suc j} u v p = ap suc p

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (suc i) = suc (toℕ i)

toℕ-sound : ∀ {n}(i : Fin n) → suc (toℕ i) ≤ n
toℕ-sound {zero} ()
toℕ-sound {suc n} zero = s≤s z≤n
toℕ-sound {suc n} (suc i) = s≤s (toℕ-sound i)

fromℕ : ∀ {n i} → (suc i ≤ n) → Fin n
fromℕ {zero} ()
fromℕ {suc n} {0} _ = zero
fromℕ {suc n} {suc i} (s≤s p) = suc (fromℕ p)

toℕ-iso : ∀ {n} → Fin n ≅ (Σ ℕ λ i → suc i ≤ n)
toℕ-iso {n} = record
  { to = λ i → toℕ i , toℕ-sound i
  ; from = λ { (_ , p) → fromℕ p }
  ; iso₁ = α
  ; iso₂ = λ { (i , p) → unapΣ (β i p , h1⇒prop ≤-level _ _) } }
  where
    α : ∀ {n} (i : Fin n) → fromℕ (toℕ-sound i) ≡ i
    α zero = refl
    α (suc i) = ap suc (α i)

    β : ∀ {n} (i : ℕ)(p : suc i ≤ n) → toℕ (fromℕ p) ≡ i
    β {0} _ ()
    β {suc n} 0 _ = refl
    β {suc n} (suc i) (s≤s p) = ap suc (β i p)

toℕ-inj : ∀ {n} → injective (toℕ {n = n})
toℕ-inj p = iso⇒inj toℕ-iso (unapΣ (p , h1⇒prop ≤-level _ _))

#_ : ∀ {n} i {p : True (suc i ≤? n)} → Fin n
#_ {n} i {p} = fromℕ (witness p)

transpose : ∀ {n} → Fin n → Fin n → Fin n → Fin n
transpose i j k with i ≟ k
... | yes _ = j
... | no _ with j ≟ k
... | yes _ = i
... | no _ = k

transpose-β₂ : ∀ {n}(i j : Fin n)
             → transpose i j j ≡ i
transpose-β₂ i j with i ≟ j
... | yes p = sym p
... | no u with j ≟ j
... | yes p = refl
... | no v = ⊥-elim (v refl)

abstract
  transpose-invol : ∀ {n}(i j k : Fin n)
                  → transpose i j (transpose i j k) ≡ k
  transpose-invol i j k with i ≟ k
  transpose-invol i j k | yes p with i ≟ j
  transpose-invol i j k | yes p | yes p' = sym p' · p
  transpose-invol i j k | yes p | no u with j ≟ j
  transpose-invol i j k | yes p | no u | yes p' = p
  transpose-invol i j k | yes p | no u | no v = ⊥-elim (v refl)
  transpose-invol i j k | no u with j ≟ k
  transpose-invol i j k | no u | yes p with i ≟ i
  transpose-invol i j k | no u | yes p | yes p' = p
  transpose-invol i j k | no u | yes p | no v = ⊥-elim (v refl)
  transpose-invol i j k | no u | no v with i ≟ k
  transpose-invol i j k | no u | no v | yes p = ⊥-elim (u p)
  transpose-invol i j k | no u | no v | no w with j ≟ k
  transpose-invol i j k | no u | no v | no w | yes p = ⊥-elim (v p)
  transpose-invol i j k | no u | no v | no w | no z = refl

transpose-iso : ∀ {n}(i j : Fin n) → Fin n ≅ Fin n
transpose-iso i j = record
  { to = transpose i j
  ; from = transpose i j
  ; iso₁ = transpose-invol i j
  ; iso₂ = transpose-invol i j }

fin-remove₀-iso : ∀ {n} → (Fin (suc n) minus zero) ≅ Fin n
fin-remove₀-iso = record
  { to = uncurry pred
  ; from = λ i → suc i , λ p → fin-disj _ (sym p)
  ; iso₁ = λ { (i , u) → unapΣ (pred-β _ u , h1⇒prop ¬-h1 _ _) }
  ; iso₂ = λ _ → refl }

fin-remove-iso : ∀ {n}(i : Fin (suc n))
               → (Σ (Fin (suc n)) λ j → ¬ (j ≡ i))
               ≅ Fin n
fin-remove-iso {n} i = begin
    (Σ (Fin (suc n)) λ j → ¬ (j ≡ i))
  ≅⟨ ( Σ-ap-iso (transpose-iso zero i) λ _
     → Π-ap-iso lem λ _ → refl≅ ) ⟩
    (Σ (Fin (suc n)) λ j → ¬ (j ≡ zero))
  ≅⟨ fin-remove₀-iso ⟩
    Fin n
  ∎
  where
    open ≅-Reasoning

    lem : ∀ {x} → (x ≡ i) ≅ (transpose zero i x ≡ zero)
    lem {x} = begin
        (x ≡ i)
      ≅⟨ iso≡ (transpose-iso zero i) ⟩
        ( transpose zero i x ≡ transpose zero i i )
      ≅⟨ trans≡-iso' (transpose-β₂ zero i) ⟩
        ( transpose zero i x ≡ zero )
      ∎ where open ≅-Reasoning

transpose-inj : ∀ {n m}(i j : Fin m)
              → (f : Fin n → Fin m)
              → injective f
              → injective (transpose i j ∘' f)
transpose-inj i j f inj = inj ∘' iso⇒inj (transpose-iso i j)

transpose-inj-iso' : ∀ {n} (i j : Fin n)
                   → (Fin n ↣ Fin n)
                   ≅ (Fin n ↣ Fin n)
transpose-inj-iso' {n} i j
  = Σ-ap-iso (Π-ap-iso refl≅ λ _ → tiso) λ f
  → mk-prop-iso (inj-level f (fin-set _))
                (inj-level _ (fin-set _))
                (transpose-inj i j f)
                (λ inj p → inj (ap (apply tiso) p))
   where
     tiso : Fin n ≅ Fin n
     tiso = transpose-iso i j


transpose-inj-iso : ∀ {n} (i j : Fin n)
                  → (Fin n ↣ Fin n)
                  ≅ (Fin n ↣ Fin n)
transpose-inj-iso {n} i j
  = Σ-ap-iso (Π-ap-iso tiso λ _ → refl≅) λ f
  → mk-prop-iso (inj-level f (fin-set _))
                (inj-level _ (fin-set _))
                (λ inj → iso⇒inj tiso ∘' inj)
                (λ inj p → iso⇒inj tiso (inj (
                           ap f (_≅_.iso₁ tiso _)
                         · p
                         · sym (ap f (_≅_.iso₁ tiso _)))))
   where
     tiso : Fin n ≅ Fin n
     tiso = transpose-iso i j

inj-nonsurj : ∀ {n i}{A : Set i}
            → (f : A → Fin (suc n))
            → injective f
            → {i : Fin (suc n)}
            → ((x : A) → ¬ (f x ≡ i))
            → A ↣ Fin n
inj-nonsurj {n}{i}{A} f inj {z} u = g , g-inj
  where
    f' : A → Σ (Fin (suc n)) λ k → ¬ (k ≡ z)
    f' i = f i , u i

    inj' : injective f'
    inj' p = inj (ap proj₁ p)

    g : A → Fin n
    g = apply (fin-remove-iso z) ∘' f'

    g-inj : injective g
    g-inj p = inj' (iso⇒inj (fin-remove-iso z) p)

preimage : ∀ {i n}{A : Set i}
         → (f : Fin n → A)
         → (dec : (x y : A) → Dec (x ≡ y))
         → (x : A)
         → ( (Σ (Fin n) λ i → f i ≡ x)
            ⊎ ((i : Fin n) → ¬ (f i ≡ x)) )
preimage {n = 0} f dec x = inj₂ (λ ())
preimage {n = suc n} f dec x with dec (f zero) x
... | yes p = inj₁ (zero , p)
... | no u with preimage (λ i → f (suc i)) dec x
... | inj₁ (i , p) = inj₁ (suc i , p)
... | inj₂ v = inj₂ λ { zero → u ; (suc i) → v i }

fin-inj-remove₀ : ∀ {n m}
                → (f : Fin (suc n) ↣ Fin (suc m))
                → (apply f zero ≡ zero)
                → Fin n ↣ Fin m
fin-inj-remove₀ {n}{m} (f , inj) p = g , g-inj
  where
    nz : {i : Fin n} → ¬ (f (suc i) ≡ zero)
    nz q = fin-disj _ (inj (p · sym q))

    g : Fin n → Fin m
    g i = pred (f (suc i)) nz

    g-inj : injective g
    g-inj q = fin-suc-inj (inj (pred-inj nz nz q))

fin-inj-remove : ∀ {n m}
               → (Fin (suc n) ↣ Fin (suc m))
               → (Fin n ↣ Fin m)
fin-inj-remove {n}{m} (f , f-inj)
  = fin-inj-remove₀
      ( transpose zero (f zero) ∘' f
      , transpose-inj zero (f zero) f f-inj)
      ( transpose-β₂ zero (f zero))

fin-inj-add : ∀ {n m}
            → (Fin n ↣ Fin m)
            → (Fin (suc n) ↣ Fin (suc m))
fin-inj-add {n}{m} (f , f-inj) = g , g-inj
  where
    g : Fin (suc n) → Fin (suc m)
    g zero = zero
    g (suc i) = suc (f i)

    g-inj : injective g
    g-inj {zero} {zero} p = refl
    g-inj {zero} {suc x'} p = ⊥-elim (fin-disj _ p)
    g-inj {suc x} {zero} p = ⊥-elim (fin-disj _ (sym p))
    g-inj {suc x} {suc x'} p = ap suc (f-inj (fin-suc-inj p))

fin-lt : ∀ {n m}(f : Fin n ↣ Fin m) → n ≤ m
fin-lt {0} _ = z≤n
fin-lt {suc n} {0} (f , _) with f zero
... | ()
fin-lt {suc n}{suc m} f = s≤s (fin-lt (fin-inj-remove f))

inj⇒retr : ∀ {n}(f : Fin n → Fin n)
         → injective f
         → retraction f
inj⇒retr {0} f inj ()
inj⇒retr {suc n} f inj y with preimage f _≟_ y
... | inj₁ t = t
... | inj₂ u = ⊥-elim (suc≰ (fin-lt (inj-nonsurj f inj u)))

inj⇒iso : ∀ {n}(f : Fin n → Fin n)
         → injective f
         → Fin n ≅ Fin n
inj⇒iso f inj = inj+retr⇒iso f inj (inj⇒retr f inj)

Fin-inj : ∀ {n m} → Fin n ≅ Fin m → n ≡ m
Fin-inj {n}{m} isoF
  = antisym≤ (fin-lt (_ , iso⇒inj isoF))
             (fin-lt (_ , iso⇒inj (sym≅ isoF)))
