{-# OPTIONS --without-K --type-in-type #-}
module function.isomorphism.coherent where

open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import function.isomorphism.core

coherent : {X : Set}{Y : Set} → X ≅ Y → Set
coherent f = ∀ x → ap to (iso₁ x) ≡ iso₂ (to x)
  -- this definition says that the two possible proofs that
  --     to (from (to x)) ≡ to x
  -- are equal
  where
    open _≅_ f

coherent' : {X : Set}{Y : Set} → X ≅ Y → Set
coherent' f = ∀ y → ap from (iso₂ y) ≡ iso₁ (from y)
  where
    open _≅_ f

-- coherent isomorphisms
_≅'_ : (X Y : Set) → Set
X ≅' Y = Σ (X ≅ Y) coherent

-- technical lemma: substiting a fixpoint proof into itself is like
-- applying the function
lem-subst-fixpoint : {X : Set}
                     (f : X → X)(x : X)
                     (p : f x ≡ x)
                   → subst (λ x → f x ≡ x) (sym p) p
                   ≡ ap f p
lem-subst-fixpoint {X} f x p = begin
    subst (λ x → f x ≡ x) (p ⁻¹) p
  ≡⟨ lem (f x) (sym p) ⟩
    ap f (sym (sym p)) · p · sym p
  ≡⟨ ap (λ z → ap f z · p · sym p)
           (double-inverse p) ⟩
    ap f p · p · sym p
  ≡⟨ associativity (ap f p) p (sym p) ⟩
    ap f p · (p · sym p)
  ≡⟨ ap (λ z → ap f p · z) (left-inverse p) ⟩
    ap f p · refl
  ≡⟨ left-unit (ap f p) ⟩
    ap f p
  ∎
  where
    open ≡-Reasoning
    lem : (y : X) (q : x ≡ y)
        → subst (λ z → f z ≡ z) q p
        ≡ ap f (sym q) · p · q
    lem .x refl = sym (left-unit p)

lem-whiskering : {X : Set}
                 (f : X → X) (H : (x : X) → f x ≡ x)
                 (x : X) → ap f (H x) ≡ H (f x)
lem-whiskering f H x = begin
    ap f (H x)
  ≡⟨ sym (lem-subst-fixpoint f x (H x)) ⟩
    subst (λ z → f z ≡ z) (sym (H x)) (H x)
  ≡⟨ ap' H (sym (H x)) ⟩
    H (f x)
  ∎
  where
    open ≡-Reasoning

lem-homotopy-nat : {X Y : Set}
                   {x x' : X}{f g : X → Y}
                   (H : (x : X) → f x ≡ g x) (p : x ≡ x')
                 → H x · ap g p ≡ ap f p · H x'
lem-homotopy-nat H refl = left-unit _

co-coherence : {X Y : Set}
               (isom : X ≅ Y)
             → coherent isom
             → coherent' isom
co-coherence (iso f g H K) coherence y =
  subst (λ z → ap g (K z) ≡ H (g z)) (K y) lem
  where
    open ≡-Reasoning

    lem : ap g (K (f (g y)))
        ≡ H (g (f (g y)))
    lem = begin
        ap g (K (f (g y)))
      ≡⟨ ap (ap g) (sym (coherence (g y))) ⟩
        ap g (ap f (H (g y)))
      ≡⟨ ap-hom f g _ ⟩
        ap (g ∘ f) (H (g y))
      ≡⟨ lem-whiskering (g ∘ f) H (g y) ⟩
        H (g (f (g y)))
      ∎

sym≅' : {X Y : Set}
      → X ≅' Y → Y ≅' X
sym≅' (isom , γ) = sym≅ isom , co-coherence isom γ

--- Vogt's lemma. See http://ncatlab.org/nlab/show/homotopy+equivalence
vogt-lemma : {X Y : Set} → (isom : X ≅ Y)
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
    --     K' = (f g K) ⁻¹ · (f H g f) · (K f)
    --
    -- we get that K' f must be equal to the bottom row, which is
    -- exactly the required coherence condition.

    open ≡-Reasoning

    -- the diagram above commutes
    lem : (x : X)
        → ap f (H (g (f x))) · K (f x)
        ≡ ap (f ∘ g) (K (f x)) · ap f (H x)
    lem x = begin
        ap f (H (g (f x))) · K (f x)
      ≡⟨ ap (λ z → ap f z · K (f x))
              (sym (lem-whiskering (g ∘ f) H x)) ⟩
        ap f (ap (g ∘ f) (H x)) · K (f x)
      ≡⟨ ap (λ z → z · K (f x))
              (ap-hom (g ∘ f) f (H x)) ⟩
        ap (f ∘ g ∘ f) (H x) · K (f x)
      ≡⟨ sym (lem-homotopy-nat (λ x → K (f x)) (H x)) ⟩
        K (f (g (f x))) · ap f (H x)
      ≡⟨ ap (λ z → z · ap f (H x))
              (sym (lem-whiskering (f ∘ g) K (f x))) ⟩
        ap (f ∘ g) (K (f x)) · ap f (H x)
      ∎

    K' : (y : Y) → f (g y) ≡ y
    K' y = ap (f ∘ g) (sym (K y))
         · ap f (H (g y))
         · K y

    iso' = iso f g H K'

    -- now we can just compute using the groupoid laws
    γ : coherent iso'
    γ x = sym $ begin
        K' (f x)
      ≡⟨ refl ⟩
        ap (f ∘ g) (sym (K (f x))) ·
        ap f (H (g (f x))) · K (f x)
      ≡⟨ associativity (ap (f ∘ g) (sym (K (f x))))
               (ap f (H (g (f x))))
               (K (f x)) ⟩
        ap (f ∘ g) (sym (K (f x))) ·
        (ap f (H (g (f x))) · K (f x))
      ≡⟨ ap (λ z → ap (f ∘ g) (sym (K (f x))) · z) (lem x) ⟩
        ap (f ∘ g) (sym (K (f x))) ·
        (ap (f ∘ g) (K (f x)) · ap f (H x))
      ≡⟨ ap (λ z → z · (ap (f ∘ g) (K (f x)) · ap f (H x)))
              (ap-inv (f ∘ g) (K (f x))) ⟩
        sym (ap (f ∘ g) (K (f x))) ·
        (ap (f ∘ g) (K (f x)) · ap f (H x))
      ≡⟨ sym (associativity (sym (ap (f ∘ g) (K (f x))))
                       (ap (f ∘ g) (K (f x)))
                       (ap f (H x))) ⟩
        ( sym (ap (f ∘ g) (K (f x))) ·
          ap (f ∘ g) (K (f x)) ) ·
        ap f (H x)
      ≡⟨ ap (λ z → z · ap f (H x))
               (right-inverse (ap (f ∘ g) (K (f x)))) ⟩
        refl · ap f (H x)
      ≡⟨ right-unit (ap f (H x)) ⟩
        ap f (H x)
      ∎

≅⇒≅' : {X Y : Set} → X ≅ Y → X ≅' Y
≅⇒≅' {X = X}{Y = Y} isom = iso to from iso₁ (proj₁ v) , proj₂ v
  where
    open _≅_ isom
    open import sum
    abstract
      v : Σ ((y : Y) → to (from y) ≡ y) λ iso₂'
        → coherent (iso to from iso₁ iso₂')
      v = vogt-lemma isom
