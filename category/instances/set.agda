{-# OPTIONS --type-in-type --without-K #-}

module category.instances.set where

open import level
open import sum
open import equality.core
open import equality.calculus
open import function.core
open import function.isomorphism
open import function.extensionality
open import function.overloading
open import category.category
open import category.isomorphism
open import category.univalence
open import hott.hlevel
open import hott.weak-equivalence
open import hott.univalence

set : Category
set = mk-category record
  { obj = HSet
  ; hom = λ A B → proj₁ A → proj₁ B
  ; id = λ _ x → x
  ; _∘_ = _∘_
  ; left-id = λ _ → refl
  ; right-id = λ _ → refl
  ; assoc = λ _ _ _ → refl
  ; trunc = λ { _ B → Π-hlevel λ _ → proj₂ B }  }

-- isomorphism in the category of sets is the same
-- as isomorphism of types
cat-iso-h2 : {A B : HSet}
           → (proj₁ A ≅ proj₁ B)
           ≅ cat-iso set A B
cat-iso-h2 = record
  { to = λ { (iso f g H K) → (c-iso f g (ext' H) (ext' K)) }
  ; from = λ { (c-iso f g H K) → (iso f g (ext-inv H) (ext-inv K)) }
  ; iso₁ = λ { (iso f g H K)
             → cong (λ { ((f , g) , (H , K)) → iso f g H K })
                       (uncongΣ (refl , cong₂ _,_
                        (ext' λ x → ext-inv (_≅_.iso₁ strong-ext-iso H) x)
                        (ext' λ x → ext-inv (_≅_.iso₁ strong-ext-iso K) x))) }
  ; iso₂ = λ _ → cat-iso-equality refl refl }

-- equality of HSets is the same as equality of the underlying types
hset-equality : {A B : HSet} → (A ≡ B)
              ≅ (proj₁ A ≡ proj₁ B)
hset-equality {A = A}{B = B} = record
  { to = cong proj₁
  ; from = λ p → uncongΣ (p , proj₁ (hn-h1 2 _ _ _))
  ; iso₁ = iso₁ A B
  ; iso₂ = λ p → lem p _ }
  where
    iso₁ : (A B : HSet)(p : A ≡ B)
         → uncongΣ (cong proj₁ p , proj₁ (hn-h1 2 _ _ _)) ≡ p
    iso₁ (A , hA) .(A , hA) refl =
      cong (λ q → uncongΣ (refl , q))
           (proj₁ (h↑ (hn-h1 2 A) hA hA _ refl))

    lem : {A : Set}{B : A → Set}
          {x x' : A}{y : B x}{y' : B x'}
          (p : x ≡ x')(q : subst B p y ≡ y')
        → cong proj₁ (uncongΣ {B = B} (p , q)) ≡ p
    lem refl refl = refl

-- isomorphisms between hsets are automatically coherent
iso-coherence-h2 : {A B : HSet}
                 → (proj₁ A ≅' proj₁ B)
                 ≅ (proj₁ A ≅ proj₁ B)
iso-coherence-h2 {A = A , hA}{B = B , hB} =
  lem-contr (λ _ → Π-hlevel λ x → hB _ _ _ _)
  where
    lem-contr : {A : Set}{B : A → Set}
              → ((x : A) → contr (B x))
              → Σ A B ≅ A
    lem-contr cB = record
      { to = proj₁
      ; from = λ a → a , proj₁ (cB a)
      ; iso₁ = λ { (a , b) → uncongΣ (refl , proj₂ (cB a) b) }
      ; iso₂ = λ _ → refl }

set-univ : univalent set
set-univ = λ A B →
  lem (≡⇒iso set {A}{B})
      (lem-iso A B)
      (ext (lem-iso-comp A B))
  where
    open ≅-Reasoning

    -- the function corresponding to an isomorphism is a weak
    -- equivalence
    lem : {X Y : Set}
          (f : X → Y)(isom : X ≅ Y)
        → (apply isom ≡ f)
        → weak-equiv f
    lem {X = X}{Y = Y} .(apply isom) isom refl =
      proj₂ (≅⇒≈ isom)

    -- equality in the category of sets is the same as isomorphism
    lem-iso : (A B : HSet) → (A ≡ B) ≅ cat-iso set A B
    lem-iso (A , hA) (B , hB) = begin
        (A , hA) ≡ (B , hB)
      ≅⟨ hset-equality ⟩
        A ≡ B
      ≅⟨ uni-iso ⟩
        A ≈ B
      ≅⟨ ≈⇔≅' ⟩
        A ≅' B
      ≅⟨ iso-coherence-h2 {A = A , hA}
                          {B = B , hB}⟩
        A ≅ B
      ≅⟨ cat-iso-h2 ⟩
        cat-iso set (A , hA) (B , hB)
      ∎

    -- the above isomorphism is given by ≡⇒iso
    lem-iso-comp : (A B : HSet)(p : A ≡ B)
                 → apply (lem-iso A B) p
                 ≡ ≡⇒iso set p
    lem-iso-comp A .A refl =
      cong₂ (c-iso (λ x → x) (λ x → x))
            (ext-id' _) (ext-id' _)
