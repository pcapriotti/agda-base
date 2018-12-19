{-# OPTIONS --without-K #-}
open import level
open import algebra.group.core
open import algebra.monoid.mset
open import algebra.monoid.morphism
open import function.extensionality
open import function.isomorphism
open import equality.calculus
open import equality.core
open import sum
open import hott.level
open import hott.equivalence
open import hott.univalence

module algebra.group.gset {i}(G : Set i) ⦃ gG : IsGroup G ⦄ where
  open IsGroup ⦃ ... ⦄

  IsGSet : ∀ {j}(X : Set j) → Set (i ⊔ j)
  IsGSet X = IsMSet G X

  GSet : ∀ j → Set (i ⊔ lsuc j)
  GSet j = Σ (Set j) IsGSet

  GSet₀ : ∀ j → Set (i ⊔ lsuc j)
  GSet₀ j = Σ (Type j 2) λ { (X , hX) → G → X → X }

  GSet₁ : ∀ {j} → GSet₀ j → Set (i ⊔ j)
  GSet₁ ((X , _) , _◂_) =
    ((g₁ g₂ : G)(x : X) → (g₁ * g₂) ◂ x ≡ g₁ ◂ (g₂ ◂ x))
    × ((x : X) → e ◂ x ≡ x)

  gset₁-level : ∀ {j}(X : GSet₀ j)
              → h 1 (GSet₁ X)
  gset₁-level ((X , hX) , act) = ×-level
    (Π-level λ g₁ → Π-level λ g₂ → Π-level λ x → hX _ _)
    (Π-level λ x → hX _ _)

  gset-struct-iso : ∀ {j} → GSet j ≅ Σ (GSet₀ j) GSet₁
  gset-struct-iso = record
    { to = λ { (X , xG) → (((X , IsMSet.mset-level xG) , IsMSet._◂_ xG) ,
                           (IsMSet.◂-hom xG , IsMSet.◂-id xG)) }
    ; from = λ { (((X , hX) , _◂_) , (◂-hom , ◂-id))
             → (X , mk-is-mset _◂_ ◂-hom ◂-id hX) }
    ; iso₁ = λ _ → refl
    ; iso₂ = λ _ → refl }

  open IsMSet ⦃ ... ⦄

  module _ {j k}
           {X : Set j} ⦃ xG : IsGSet X ⦄
           {Y : Set k} ⦃ yG : IsGSet Y ⦄ where
    IsGSetMorphism : (X → Y) → Set (i ⊔ j ⊔ k)
    IsGSetMorphism = IsMSetMorphism G

  module _ {j k}
           (X : Set j) ⦃ xG : IsGSet X ⦄
           (Y : Set k) ⦃ yG : IsGSet Y ⦄ where
    GSetMorphism : Set (i ⊔ j ⊔ k)
    GSetMorphism = Σ (X → Y) IsGSetMorphism

    gsetmorphism-equality : h 2 Y → {f g : X → Y}
      (f-mor : IsGSetMorphism f) (g-mor : IsGSetMorphism g)
      → f ≡ g
      → _≡_ {A = GSetMorphism}
        (f , f-mor)
        (g , g-mor)
    gsetmorphism-equality hY {f} f-mor g-mor refl =
      ap (λ m → (f , m)) (h1⇒prop (is-mset-morphism-level G hY f) _ _)

  module _ {j} (X : Set j) ⦃ xG : IsGSet X ⦄
               (Y : Set j) ⦃ yG : IsGSet Y ⦄ where
    𝑋 𝑌 : GSet j
    𝑋 = (X , xG)
    𝑌 = (Y , yG)

    X₀ Y₀ : GSet₀ j
    X₀ = ((X , IsMSet.mset-level xG) , _◂_)
    Y₀ = ((Y , IsMSet.mset-level yG) , _◂_)

    GSet-univalence : (𝑋 ≡ 𝑌)
                    ≅ (Σ (GSetMorphism X Y) λ { (f , _) → weak-equiv f })
    GSet-univalence = begin
        (𝑋 ≡ 𝑌)
      ≅⟨ iso≡ gset-struct-iso ·≅ sym≅ (subtype-equality gset₁-level) ⟩
        (X₀ ≡ Y₀)
      ≅⟨ sym≅ Σ-split-iso ⟩
        ( Σ (proj₁ X₀ ≡ proj₁ Y₀) λ p →
            subst (λ { (X , _) → G → X → X }) p (proj₂ X₀) ≡ proj₂ Y₀ )
      ≅⟨ ( Σ-ap-iso (sym≅ (subtype-equality λ X → hn-h1 2 X)) λ p
         → trans≡-iso (sym (subst-naturality (λ X → G → X → X)
                             proj₁ p (proj₂ X₀)))) ⟩
        ( Σ (X ≡ Y) λ p → subst (λ X → G → X → X) p (proj₂ X₀) ≡ proj₂ Y₀ )
      ≅⟨ Σ-ap-iso refl≅ (λ p → sym≅ (lem₁ p _ _)) ⟩
        ( Σ (X ≡ Y) λ p → ∀ g w → coerce p (proj₂ X₀ g w)
                                ≡ proj₂ Y₀ g (coerce p w) )
      ≅⟨ ( Σ-ap-iso uni-iso λ p → refl≅ ) ⟩
        ( Σ (X ≈ Y) λ f → ∀ g w → apply≈ f (proj₂ X₀ g w)
                                ≡ proj₂ Y₀ g (apply≈ f w))
      ≅⟨  record
            { to = λ { ((f , we), mor) → ((f , mor) , we) }
            ; from = λ { ((f , mor) , we) → ((f , we) , mor) }
            ; iso₁ = λ _ → refl
            ; iso₂ = λ _ → refl } ⟩
        (Σ (GSetMorphism X Y) λ { (f , _) → weak-equiv f })
      ∎
      where
        open ≅-Reasoning

        lem₁ : {U V : Set j}(p : U ≡ V)
             → (act : G → U → U)
             → (act' : G → V → V)
             → (∀ g u → coerce p (act g u) ≡ act' g (coerce p u))
             ≅ (subst (λ { X → G → X → X }) p act ≡ act')
        lem₁ refl act act' = (Π-ap-iso refl≅ λ g → strong-funext-iso)
          ·≅ strong-funext-iso

  instance
    GisGSet : IsGSet G
    GisGSet = record
      { _◂_ = _*_
      ; ◂-hom = assoc
      ; ◂-id = lunit
      ; mset-level = is-set }

  module _ {j} {X : Set j} (hX : h 2 X) ⦃ xG : IsGSet X ⦄ where
    GSet-repr : (ϕ : G → X) → IsGSetMorphism ϕ
              → (g : G) → ϕ g ≡ g ◂ ϕ e
    GSet-repr ϕ ϕ-mor g = ap ϕ (sym (runit g)) · ϕ-mor g e

    GSet-repr-iso : GSetMorphism G X ≅ X
    GSet-repr-iso = iso f g α β
      where
        f : GSetMorphism G X → X
        f (ϕ , _) = ϕ e

        g : X → GSetMorphism G X
        g x = (ϕ , ϕ-mor)
          where
            ϕ : G → X
            ϕ g = g ◂ x

            ϕ-mor : IsGSetMorphism ϕ
            ϕ-mor g₁ g₂ = ◂-hom g₁ g₂ x

        α : (ϕ : GSetMorphism G X) → g (f ϕ) ≡ ϕ
        α (ϕ , ϕ-mor) = gsetmorphism-equality G X hX _ _
          (funext λ g → sym (GSet-repr ϕ ϕ-mor g))

        β : (x : X) → f (g x) ≡ x
        β x = (IsMSet.◂-id xG) x
