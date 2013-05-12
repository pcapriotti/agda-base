{-# OPTIONS --without-K #-}
module function.isomorphism.coherent where

open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.isomorphism.core
open import function.overloading
open import overloading.core

coherent : ∀ {i j} {X : Set i}{Y : Set j} → X ≅ Y → Set _
coherent f = ∀ x → cong to (iso₁ x) ≡ iso₂ (to x)
  -- this definition says that the two possible proofs that
  --     to (from (to x)) ≡ to x
  -- are equal
  where
    open _≅_ f

coherent' : ∀ {i j} {X : Set i}{Y : Set j} → X ≅ Y → Set _
coherent' f = ∀ y → cong from (iso₂ y) ≡ iso₁ (from y)
  where
    open _≅_ f

-- coherent isomorphisms
_≅'_ : ∀ {i j} → (X : Set i)(Y : Set j) → Set _
X ≅' Y = Σ (X ≅ Y) coherent

iso'-is-fun : ∀ {i j}{X : Set i}{Y : Set j}
            → Coercion (X ≅' Y) (X → Y)
iso'-is-fun = record
  { coerce = λ isom → apply (proj₁ isom) }


iso'-is-iso : ∀ {i j}{X : Set i}{Y : Set j}
            → Coercion (X ≅' Y) (X ≅ Y)
iso'-is-iso = record
  { coerce = proj₁ }

-- technical lemma: substiting a fixpoint proof into itself is like
-- applying the function
lem-subst-fixpoint : ∀ {i}{X : Set i}
                     (f : X → X)(x : X)
                     (p : f x ≡ x)
                   → subst (λ x → f x ≡ x) (sym p) p
                   ≡ cong f p
lem-subst-fixpoint {i}{X} f x p = begin
    subst (λ x → f x ≡ x) (p ⁻¹) p
  ≡⟨ lem (f x) (sym p) ⟩ 
    cong f (sym (sym p)) ⊚ p ⊚ sym p
  ≡⟨ cong (λ z → cong f z ⊚ p ⊚ sym p)
           (double-inverse p) ⟩
    cong f p ⊚ p ⊚ sym p
  ≡⟨ associativity (cong f p) p (sym p) ⟩
    cong f p ⊚ (p ⊚ sym p)
  ≡⟨ cong (λ z → cong f p ⊚ z) (left-inverse p) ⟩
    cong f p ⊚ refl
  ≡⟨ left-unit (cong f p) ⟩
    cong f p
  ∎
  where
    open ≡-Reasoning
    lem : (y : X) (q : x ≡ y)
        → subst (λ z → f z ≡ z) q p
        ≡ cong f (sym q) ⊚ p ⊚ q
    lem .x refl = sym (left-unit p)

lem-whiskering : ∀ {i} {X : Set i}
                 (f : X → X) (H : (x : X) → f x ≡ x)
                 (x : X) → cong f (H x) ≡ H (f x)
lem-whiskering f H x = begin
    cong f (H x)
  ≡⟨ sym (lem-subst-fixpoint f x (H x)) ⟩
    subst (λ z → f z ≡ z) (sym (H x)) (H x)
  ≡⟨ cong' H (sym (H x)) ⟩
    H (f x)
  ∎
  where
    open ≡-Reasoning

lem-homotopy-nat : ∀ {i j}{X : Set i}{Y : Set j}
                   {x x' : X}{f g : X → Y}
                   (H : (x : X) → f x ≡ g x) (p : x ≡ x')
                 → H x ⊚ cong g p ≡ cong f p ⊚ H x'
lem-homotopy-nat H refl = left-unit _

co-coherence : ∀ {i j}{X : Set i}{Y : Set j}
               (isom : X ≅ Y)
             → coherent isom
             → coherent' isom
co-coherence (iso f g H K) coherence y =
  subst (λ z → cong g (K z) ≡ H (g z)) (K y) lem
  where
    open ≡-Reasoning

    lem : cong g (K (f (g y)))
        ≡ H (g (f (g y)))
    lem = begin
        cong g (K (f (g y)))
      ≡⟨ cong (cong g) (sym (coherence (g y))) ⟩
        cong g (cong f (H (g y)))
      ≡⟨ cong-hom f g _ ⟩
        cong (g ∘ f) (H (g y))
      ≡⟨ lem-whiskering (g ∘ f) H (g y) ⟩
        H (g (f (g y)))
      ∎

sym≅' : ∀ {i j}{X : Set i}{Y : Set j}
      → X ≅' Y → Y ≅' X
sym≅' (isom , γ) = sym≅ isom , co-coherence isom γ

--- Vogt's lemma. See http://ncatlab.org/nlab/show/homotopy+equivalence
vogt-lemma : ∀ {i j}{X : Set i}{Y : Set j} → (isom : X ≅ Y)
           → let open _≅_ isom
              in Σ ((y : Y) → to (from y) ≡ y) λ iso' →
                 coherent (iso to from iso₁ iso')
vogt-lemma {X = X}{Y = Y} isom = K' , γ
  where
    open _≅_ isom
      renaming (to to f ; from to g ; iso₁ to H ; iso₂ to K)

    -- Outline of the proof
    -- --------------------
    --
    -- We want to find a homotopy K' : f g → id such that f K' ≡ H f.
    --
    -- To do so, we first prove that the following diagram of
    -- homotopies:
    --
    --                     f H g f
    --          f g f g f ---------> f g f
    --              |                  |
    --     f g K f  |                  | K f
    --              |                  |
    --              v                  v
    --            f g f -------------> f
    --                       f H
    --
    -- commutes. We then observe that f appears on the right side of
    -- every element in the diagram, except the bottom row, so if we
    -- define:
    --
    --     K' = (f g K) ⁻¹ ⊚ (f H g f) ⊚ (K f)
    --
    -- we get that K' f must be equal to the bottom row, which is
    -- exactly the required coherence condition.

    open ≡-Reasoning

    -- the diagram above commutes
    lem : (x : X)
        → cong f (H (g (f x))) ⊚ K (f x)
        ≡ cong (f ∘ g) (K (f x)) ⊚ cong f (H x)
    lem x = begin
        cong f (H (g (f x))) ⊚ K (f x)
      ≡⟨ cong (λ z → cong f z ⊚ K (f x))
              (sym (lem-whiskering (g ∘ f) H x)) ⟩
        cong f (cong (g ∘ f) (H x)) ⊚ K (f x)
      ≡⟨ cong (λ z → z ⊚ K (f x))
              (cong-hom (g ∘ f) f (H x)) ⟩
        cong (f ∘ g ∘ f) (H x) ⊚ K (f x)
      ≡⟨ sym (lem-homotopy-nat (λ x → K (f x)) (H x)) ⟩
        K (f (g (f x))) ⊚ cong f (H x)
      ≡⟨ cong (λ z → z ⊚ cong f (H x))
              (sym (lem-whiskering (f ∘ g) K (f x))) ⟩
        cong (f ∘ g) (K (f x)) ⊚ cong f (H x)
      ∎

    K' : (y : Y) → f (g y) ≡ y
    K' y = cong (f ∘ g) (sym (K y))
         ⊚ cong f (H (g y))
         ⊚ K y

    iso' = iso f g H K'

    -- now we can just compute using the groupoid laws
    γ : coherent iso'
    γ x = sym $ begin
        K' (f x)
      ≡⟨ refl ⟩
        cong (f ∘ g) (sym (K (f x))) ⊚
        cong f (H (g (f x))) ⊚ K (f x)
      ≡⟨ associativity (cong (f ∘ g) (sym (K (f x))))
               (cong f (H (g (f x))))
               (K (f x)) ⟩
        cong (f ∘ g) (sym (K (f x))) ⊚
        (cong f (H (g (f x))) ⊚ K (f x))
      ≡⟨ cong (λ z → cong (f ∘ g) (sym (K (f x))) ⊚ z) (lem x) ⟩
        cong (f ∘ g) (sym (K (f x))) ⊚
        (cong (f ∘ g) (K (f x)) ⊚ cong f (H x))
      ≡⟨ cong (λ z → z ⊚ (cong (f ∘ g) (K (f x)) ⊚ cong f (H x)))
              (cong-inv (f ∘ g) (K (f x))) ⟩
        sym (cong (f ∘ g) (K (f x))) ⊚
        (cong (f ∘ g) (K (f x)) ⊚ cong f (H x))
      ≡⟨ sym (associativity (sym (cong (f ∘ g) (K (f x))))
                       (cong (f ∘ g) (K (f x)))
                       (cong f (H x))) ⟩
        ( sym (cong (f ∘ g) (K (f x))) ⊚
          cong (f ∘ g) (K (f x)) ) ⊚
        cong f (H x)
      ≡⟨ cong (λ z → z ⊚ cong f (H x))
               (right-inverse (cong (f ∘ g) (K (f x)))) ⟩
        refl ⊚ cong f (H x)
      ≡⟨ right-unit (cong f (H x)) ⟩
        cong f (H x)
      ∎

≅⇒≅' : ∀ {i j} {X : Set i}{Y : Set j} → X ≅ Y → X ≅' Y
≅⇒≅' {X = X}{Y = Y} isom = iso to from iso₁ (proj₁ v) , proj₂ v
  where
    open _≅_ isom
    open import sum
    abstract
      v : Σ ((y : Y) → to (from y) ≡ y) λ iso₂'
        → coherent (iso to from iso₁ iso₂')
      v = vogt-lemma isom
