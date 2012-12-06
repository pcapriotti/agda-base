{-# OPTIONS --without-K #-}
module hott.coherence where

open import equality using
  (_≡_ ; refl ; sym ; cong ; subst)
open import equality.calculus
open import equality.reasoning
open import function using (_$_ ; id ; _∘_)
open import function.isomorphism
open import sum using
  (Σ ; _,_ ; proj₁ ; proj₂)
open import hott.hlevel
open import hott.weak-equivalence
open import category.functor using (Functor)
open import category.instances.discrete

open DiscreteGroupoid hiding (id ; _∘_)

-- a coherent isomophism is one determined by a weak equivalence
isCoherent : ∀ {i j} {X : Set i}{Y : Set j} → X ≅ Y → Set _
isCoherent f = ∀ x → cong to (iso₁ x) ≡ iso₂ (to x)
  -- this definition says that the two possible proofs that
  --     to (from (to x)) ≡ to x
  -- are equal
  where
    open _≅_ f

isCoherent₂ : ∀ {i} {X Y : Set i} → X ≅ Y → Set i
isCoherent₂ f = ∀ y → cong from (iso₂ y) ≡ iso₁ (from y)
  where
    open _≅_ f

-- coherent isomorphisms
_≅'_ : ∀ {i j} → (X : Set i)(Y : Set j) → Set _
X ≅' Y = Σ (X ≅ Y) isCoherent

lem-homotopy-nat : ∀ {i j}{X : Set i}{Y : Set j}
                   {x x' : X}{f g : X → Y}
                   (H : (x : X) → f x ≡ g x) (p : x ≡ x')
                 → H x ⊚ cong g p ≡ cong f p ⊚ H x'
lem-homotopy-nat H refl = left-unit _

≅'⇒≈ : ∀ {i j}{X : Set i}{Y : Set j} → (X ≅' Y) → X ≈ Y
≅'⇒≈ {i}{j}{X}{Y} (isom , coherent) = f , we
  where
    open _≅_ isom
      renaming ( to to f ; from to g
               ; iso₁ to H ; iso₂ to K )

    contr-fiber : (y : Y)(x : X)(p : f x ≡ y)
                → Σ (x ≡ g y) λ q
                → subst (λ x → f x ≡ y) q p ≡ K y
    contr-fiber y x p = q , lem
      where
        open ≡-Reasoning
        
        q : x ≡ g y
        q = sym (H x) ⊚ cong g p

        lem : subst (λ x → f x ≡ y) q p ≡ K y
        lem = begin
            subst (λ x → f x ≡ y) q p
          ≡⟨ subst-naturality (λ x → x ≡ y) f q p ⟩
            subst (λ x → x ≡ y) (cong f q) p
          ≡⟨ subst-eq (cong f q) p ⟩
            sym (cong f q) ⊚ p
          ≡⟨ cong (λ z → z ⊚ p)
                  (sym (cong-inv f q)) ⟩
            cong f (sym q) ⊚ p
          ≡⟨ cong (λ z → cong f z ⊚ p)
                   (inverse-comp (sym (H x)) (cong g p)) ⟩
            cong f (sym (cong g p) ⊚ sym (sym (H x))) ⊚ p
          ≡⟨ cong (λ z → cong f (z ⊚ sym (sym (H x))) ⊚ p)
                  (sym (cong-inv g p)) ⟩
            cong f (cong g (sym p) ⊚ sym (sym (H x))) ⊚ p
          ≡⟨ cong (λ z → cong f (cong g (sym p) ⊚ z) ⊚ p)
                  (double-inverse (H x)) ⟩
            cong f (cong g (sym p) ⊚ H x) ⊚ p
          ≡⟨ cong (λ z → z ⊚ p)
                   (Functor.map-hom (discrete-map f) (cong g (sym p)) (H x)) ⟩
            cong f (cong g (sym p)) ⊚ cong f (H x) ⊚ p
          ≡⟨ cong (λ z → z ⊚ cong f (H x) ⊚ p)
                   (cong-hom g f (sym p)) ⟩
            cong (f ∘ g) (sym p) ⊚ cong f (H x) ⊚ p
          ≡⟨ cong (λ z → cong (f ∘ g) (sym p) ⊚ z ⊚ p) (coherent x) ⟩
            cong (f ∘ g) (sym p) ⊚ K (f x) ⊚ p
          ≡⟨ cong (λ z → z ⊚ p) (sym (lem-homotopy-nat K (sym p))) ⟩
            K y ⊚ cong id (sym p) ⊚ p
          ≡⟨ cong (λ z → K y ⊚ z ⊚ p) (cong-id (sym p)) ⟩
            K y ⊚ sym p ⊚ p
          ≡⟨ sym (associativity (K y) (sym p) p) ⟩
            K y ⊚ (sym p ⊚ p)
          ≡⟨ cong (_⊚_ (K y)) (right-inverse p) ⟩
            K y ⊚ refl
          ≡⟨ left-unit (K y) ⟩
            K y
          ∎

    we : isWeakEquiv f
    we y = (g y , K y) ,
           λ { (x , p) → sym (uncongΣ (contr-fiber y x p)) }

-- weak equivalences correspond to coherent isomorphisms
weakEquivCoherent : ∀ {i j} {X : Set i}{Y : Set j}
                  → (e : X ≈ Y) → isCoherent (≈⇒≅ e)
weakEquivCoherent {i}{j}{X}{Y} (f , we) x = main
  where
    isom : X ≅ Y
    isom = ≈⇒≅ (f , we)

    P = λ x' → f x' ≡ f x
    
    -- let g be the inverse
    open _≅_ isom renaming (from to g)

    -- we define a more general coherence property using we
    coherence : (x' : X) → (q : f x' ≡ f x)
              → Σ (x' ≡ g (f x)) λ p
              → subst P p q ≡ iso₂ (f x)
    coherence x' q =  congΣ $ sym (proj₂ (we (f x)) (x' , q))

    open import equality.reasoning
    open ≡-Reasoning

    -- we will use (coherence x refl) to prove our coherence property

    -- first, let's prove that the first component of (coherence x refl)
    -- is the same as iso₁ x (inverted)
    lem : proj₁ (coherence x refl) ≡ sym (iso₁ x)
    lem = begin
         proj₁ (coherence x refl)
      ≡⟨ congΣ-sym coh ⟩
         sym (proj₁ (congΣ coh))
      ≡⟨ cong sym (congΣ-proj coh) ⟩
         sym (iso₁ x)
      ∎
      where coh = proj₂ (we (f x)) (x , refl)

    -- then we show the main coherence property
    -- the proof is complicated by the fact that we need to invert iso₁ to make
    -- things work, but we're essentially just using the second component of
    -- coherence x refl here
    main = begin
        cong f (iso₁ x)
      ≡⟨ cong (λ z → cong f z) (sym (double-inverse (iso₁ x))) ⟩
        cong f (sym (sym (iso₁ x)))
      ≡⟨ subst-cong f (sym (iso₁ x)) ⟩
        subst (λ x' → f x' ≡ f x) (sym (iso₁ x)) refl
      ≡⟨ subst (λ z → subst P z refl ≡ iso₂ (f x))
                lem
                (proj₂ $ coherence x refl) ⟩
        iso₂ (f x)
      ∎

    -- notes
    -- 1) is it possible to remove all uses of sym here?
    -- 2) is using congΣ really necessary?

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
  ≡⟨ sym (associativity (cong f p) p (sym p)) ⟩
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

coCoherence : ∀ {i}{X Y : Set i}
              (iso : X ≅ Y)
            → isCoherent iso
            → isCoherent₂ iso
coCoherence isom coherence y =
  subst (λ z → cong g (iso₂ z) ≡ iso₁ (g z)) (iso₂ y) lem
  where
    open ≡-Reasoning
    open _≅_ isom renaming
      (to to f ; from to g)

    lem : cong g (iso₂ (f (g y)))
        ≡ iso₁ (g (f (g y)))
    lem = begin
        cong g (iso₂ (f (g y)))
      ≡⟨ cong (cong g) (sym (coherence (g y))) ⟩
        cong g (cong f (iso₁ (g y)))
      ≡⟨ cong-hom f g _ ⟩
        cong (g ∘ f) (iso₁ (g y))
      ≡⟨ lem-whiskering (g ∘ f) iso₁ (g y) ⟩
        iso₁ (g (f (g y)))
      ∎

--- Vogt's lemma. See http://ncatlab.org/nlab/show/homotopy+equivalence
vogt-lemma : ∀ {i j}{X : Set i}{Y : Set j} → (isom : X ≅ Y)
           → let open _≅_ isom
              in Σ ((y : Y) → to (from y) ≡ y) λ iso' →
                 isCoherent (iso to from iso₁ iso')
vogt-lemma {X = X}{Y = Y} isom = K' , coherent
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
    coherent : isCoherent iso'
    coherent x = sym $ begin
        K' (f x)
      ≡⟨ refl ⟩
        cong (f ∘ g) (sym (K (f x))) ⊚
        cong f (H (g (f x))) ⊚ K (f x)
      ≡⟨ sym (associativity (cong (f ∘ g) (sym (K (f x))))
               (cong f (H (g (f x))))
               (K (f x))) ⟩
        cong (f ∘ g) (sym (K (f x))) ⊚
        (cong f (H (g (f x))) ⊚ K (f x))
      ≡⟨ cong (λ z → cong (f ∘ g) (sym (K (f x))) ⊚ z) (lem x) ⟩
        cong (f ∘ g) (sym (K (f x))) ⊚
        (cong (f ∘ g) (K (f x)) ⊚ cong f (H x))
      ≡⟨ cong (λ z → z ⊚ (cong (f ∘ g) (K (f x)) ⊚ cong f (H x)))
              (cong-inv (f ∘ g) (K (f x))) ⟩
        sym (cong (f ∘ g) (K (f x))) ⊚
        (cong (f ∘ g) (K (f x)) ⊚ cong f (H x))
      ≡⟨ associativity (sym (cong (f ∘ g) (K (f x))))
                       (cong (f ∘ g) (K (f x)))
                       (cong f (H x)) ⟩
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
≅⇒≅' isom = iso to from iso₁ (proj₁ v) , proj₂ v
  where
    open _≅_ isom
    v = vogt-lemma isom
    
≈⇒≅' : ∀ {i j} {X : Set i}{Y : Set j} → X ≈ Y → X ≅' Y
≈⇒≅' f = isom , weakEquivCoherent f
  where
    isom = ≈⇒≅ f

≅⇒≈ : ∀ {i}{X Y : Set i} → X ≅ Y → X ≈ Y
≅⇒≈ = ≅'⇒≈ ∘ ≅⇒≅'

-- some conjectures:
--
-- 1) higher dimensional coherence can be defined
-- 2) weak equivalences are coherent in all dimensions
-- 3) coherent isomorphisms are the same as weak equivalences
-- 4) higher dimensional coherence follows from isCoherent

inj+surj⇒weakEquiv : ∀ {i} {X Y : Set i} (f : X → Y) → isInjective f → isSurjective f → isWeakEquiv f
inj+surj⇒weakEquiv f inj surj =
   proj₂ (≅⇒≈ (inj+surj⇒iso f inj surj))