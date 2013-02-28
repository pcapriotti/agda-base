{-# OPTIONS --without-K #-}
open import function.extensionality.core

module hott.weak-equivalence.alternative where

open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.extensionality.dependent
open import function.isomorphism.core
open import function.isomorphism.coherent
open import function.isomorphism.utils
open import hott.hlevel.core
open import hott.weak-equivalence.core
open import hott.univalence

private
  module Properties {i j}{X : Set i}{Y : Set j} where
    open ≅-Reasoning

    private
      A : (f : X → Y)(g : Y → X) → Set _
      A f g = (x : X) → g (f x) ≡ x

      B : (f : X → Y)(g : Y → X) → Set _
      B f g = (y : Y) → f (g y) ≡ y

      GB : (f : X → Y) → Set _
      GB f = Σ (Y → X) (B f)

      Φ : (f : X → Y)(g : Y → X) → Set _
      Φ f g = (y : Y)(x : X) → f x ≡ y → g y ≡ x

      Ψ : (f : X → Y)(g : Y → X)(β : B f g)(φ : Φ f g) → Set _
      Ψ f g β φ = (y : Y)(x : X)(p : f x ≡ y) → cong f (φ y x p) ⊚ p ≡ β y

      W : Set _
      W = Σ (X → Y) λ f
        → Σ (GB f) λ { (g , β)
        → Σ (Φ f g) (Ψ f g β) }

      -- isomorphism inside Π
      Π-iso : ∀ {i j j'} {X : Set i}
              {Y : X → Set j}{Y' : X → Set j'}
            → ((x : X) → Y x ≅ Y' x)
            → ((x : X) → Y x)
            ≅ ((x : X) → Y' x)
      Π-iso = Π-cong-iso ext' refl≅

      -- flipped transitivity of isomorphism
      -- makes some proofs easier to read
      _⋆_ : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
          → Y ≅ Z → X ≅ Y → X ≅ Z
      isom ⋆ isom' = trans≅ isom' isom

      -- inverse image contractible ≅ (φ , ψ)
      contr-split : (f : X → Y)(g : Y → X)(β : B f g)
                  → ((y : Y)(x : f ⁻¹ y) → (g y , β y) ≡ x)
                  ≅ Σ (Φ f g) (Ψ f g β)
      contr-split f g β = begin
          ((y : Y)(x : f ⁻¹ y) → (g y , β y) ≡ x)
        ≅⟨ (Π-iso λ y → curry-iso (λ x p → (g y , β y) ≡ (x , p))) ⟩
          ((y : Y)(x : X)(p : f x ≡ y) → (g y , β y) ≡ (x , p))
        ≅⟨ (Π-iso λ y → Π-iso λ x → Π-iso λ p
         → sym≅ (Σ-split-iso {b = β y}{b' = p})) ⟩
          ((y : Y)(x : X)(p : f x ≡ y) → Σ (g y ≡ x) λ q
                → subst (λ x → f x ≡ y) q (β y) ≡ p)
        ≅⟨ (ΠΣ-swap-iso ⋆ Π-iso λ y
         → ΠΣ-swap-iso ⋆ Π-iso λ x
         → ΠΣ-swap-iso {Z = λ p q → subst (λ x → f x ≡ y) q (β y) ≡ p}) ⟩
         ( Σ (Φ f g) λ φ
         → (y : Y)(x : X)(p : f x ≡ y)
                → subst (λ x → f x ≡ y) (φ y x p) (β y) ≡ p )
        ≅⟨ (Σ-cong-iso refl≅ λ φ
         → Π-iso λ y → Π-iso λ x → Π-iso λ p
         → lem f g β φ y x p) ⟩
          Σ (Φ f g) (Ψ f g β)
        ∎
        where
          lem : (f : X → Y)(g : Y → X)(β : (y : Y) → f (g y) ≡ y)
                (φ : (y : Y)(x : X) → f x ≡ y → g y ≡ x)
              → (y : Y)(x : X)(p : f x ≡ y)
              → (subst (λ x → f x ≡ y) (φ y x p) (β y) ≡ p)
              ≅ (cong f (φ y x p) ⊚ p ≡ β y)
          lem f g β φ y x p = begin
              subst (λ x → f x ≡ y) (φ y x p) (β y) ≡ p
            ≡⟨ cong (λ z → z ≡ p)
                    ( subst-naturality (λ x → x ≡ y) f (φ y x p) (β y)
                    ⊚ subst-eq (cong f (φ y x p)) (β y) ) ⟩
              sym (cong f (φ y x p)) ⊚ β y ≡ p
            ≅⟨ sym≅ (move-≡-iso (cong f (φ y x p)) p (β y)) ⟩
              cong f (φ y x p) ⊚ p ≡ β y
            ∎

      -- weak equivalence ≅ (f , g , β , φ , ψ)
      weak-equiv-split : (X ≈ Y) ≅ W
      weak-equiv-split =
        Σ-cong-iso refl≅ (λ f → begin
            weak-equiv f
          ≅⟨ ΠΣ-swap-iso ⟩
            Σ ((y : Y) → f ⁻¹ y) (λ { gβ
            → (y : Y)(x : f ⁻¹ y) → gβ y ≡ x })
          ≅⟨ Σ-cong-iso ΠΣ-swap-iso (λ _ → refl≅) ⟩
            ( Σ (GB f) λ { (g , β)
            → (y : Y)(x : f ⁻¹ y) → (g y , β y) ≡ x } )
          ≅⟨ Σ-cong-iso refl≅ (λ { (g , β) → contr-split f g β }) ⟩
            ( Σ (GB f) λ { (g , β)
            → Σ (Φ f g) (Ψ f g β) } )
          ∎ )

    -- weak-equivalence ≅ coherent isomorphism
    ≈⇔≅' : (X ≈ Y) ≅ (X ≅' Y)
    ≈⇔≅' = begin
        X ≈ Y
      ≅⟨ weak-equiv-split ⟩
        W
      ≅⟨ Σ-cong-iso refl≅ (λ f
         → Σ-cong-iso refl≅ λ { (g , K)
         → Σ-cong-iso {Y = Ψ f g K}
                       (φ≅H f g)
                       (λ H → ψ≅γ f g H K) }) ⟩
        ( Σ (X → Y) λ f
        → Σ (GB f) λ { (g , K)
        → Σ (A f g) λ H
        → coherent (iso f g H K) } )
      ≅⟨ iso (λ { (f , (g , K) , H , γ) → iso f g H K , γ })
             (λ { (iso f g H K , γ) → (f , (g , K) , H , γ) })
             (λ _ → refl) (λ _ → refl) ⟩
        X ≅' Y
      ∎
      where
        Ψ' : (f : X → Y)(g : Y → X)(K : B f g)(H : A f g) → Set _
        Ψ' f g K H = ((y : Y)(x : X)(p : f x ≡ y)
                   → cong f (sym (cong g p) ⊚ H x) ⊚ p ≡ K y)

        φ≅H : (f : X → Y)(g : Y → X) → Φ f g ≅ A f g
        φ≅H f g = record
          { to = λ φ x → φ (f x) x refl
          ; from = λ H y x p → sym (cong g p) ⊚ H x 
          ; iso₁ = λ φ → ext' λ y → ext' λ x → ext' λ p → lem φ y x p
          ; iso₂ = λ H → refl }
          where
            lem : (φ : (y : Y)(x : X) → f x ≡ y → g y ≡ x)
                → (y : Y)(x : X)(p : f x ≡ y)
                → sym (cong g p) ⊚ φ (f x) x refl ≡ φ y x p
            lem φ .(f x) x refl = refl

        ψ≅γ : (f : X → Y)(g : Y → X)(H : A f g)(K : B f g)
            → Ψ' f g K H ≅ coherent (iso f g H K)
        ψ≅γ f g H K = record
          { to = to
          ; from = from
          ; iso₁ = λ ψ → ext' λ y → ext' λ x → ext' λ p → lem₁ ψ y x p
          ; iso₂ = λ γ → ext' λ x → lem₂ γ x }
          where
            to : Ψ' f g K H → coherent (iso f g H K)
            to ψ x = sym (left-unit _) ⊚ ψ (f x) x refl

            from : coherent (iso f g H K) → Ψ' f g K H
            from γ .(f x) x refl = left-unit _ ⊚ γ x

            lem₁ : (ψ : Ψ' f g K H)(y : Y)(x : X)(p : f x ≡ y)
                → from (to ψ) y x p ≡ ψ y x p
            lem₁ φ .(f x) x refl =
              J (λ u v q → (z : f (g (f x)) ≡ f x)
                            (r : u ≡ z)
                         → q ⊚ (sym q ⊚ r) ≡ r)
                (λ u z r → refl) _ _
                (left-unit (cong f (H x))) _
                (φ (f x) x refl)

            lem₂ : (γ : coherent (iso f g H K))(x : X)
                 → to (from γ) x ≡ γ x
            lem₂ γ x =
              J (λ u v q → (z : f (g (f x)) ≡ f x)
                         → (r : v ≡ z)
                         → sym q ⊚ (q ⊚ r) ≡ r)
                (λ u z r → refl) _ _
                (left-unit (cong f (H x))) _
                (γ x)

    open _≅_ ≈⇔≅' public using ()
      renaming ( to to ≈⇒≅'
               ; from to ≅'⇒≈ )

    ≅⇒≈ : (X ≅ Y) → (X ≈ Y)
    ≅⇒≈ = ≅'⇒≈ ∘ ≅⇒≅'

open Properties public
