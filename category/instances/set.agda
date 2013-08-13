{-# OPTIONS --without-K #-}

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

set : ∀ i → Category (lsuc i) i
set i = mk-category record
  { obj = HSet i
  ; hom = λ A B → proj₁ A → proj₁ B
  ; id = λ _ x → x
  ; _∘_ = _∘_
  ; left-id = λ _ → refl
  ; right-id = λ _ → refl
  ; assoc = λ _ _ _ → refl
  ; trunc = λ { _ B → Π-hlevel λ _ → proj₂ B }  }

-- isomorphism in the category of sets is the same
-- as isomorphism of types
cat-iso-h2 : ∀ {i}{A B : HSet i}
           → (proj₁ A ≅ proj₁ B)
           ≅ cat-iso (set i) A B
cat-iso-h2 = record
  { to = λ { (iso f g H K) → (c-iso f g (funext H) (funext K)) }
  ; from = λ { (c-iso f g H K) → (iso f g (funext-inv H) (funext-inv K)) }
  ; iso₁ = λ { (iso f g H K)
             → ap (λ { ((f , g) , (H , K)) → iso f g H K })
                       (unapΣ (refl , ap₂ _,_
                        (funext λ x → funext-inv (_≅_.iso₁ strong-funext-iso H) x)
                        (funext λ x → funext-inv (_≅_.iso₁ strong-funext-iso K) x))) }
  ; iso₂ = λ _ → cat-iso-equality refl refl }

-- equality of HSets is the same as equality of the underlying types
hset-equality : ∀ {i}{A B : HSet i}
              → (A ≡ B)
              ≅ (proj₁ A ≡ proj₁ B)
hset-equality {i}{A = A}{B = B} = record
  { to = ap proj₁
  ; from = λ p → unapΣ (p , proj₁ (hn-h1 2 _ _ _))
  ; iso₁ = iso₁ A B
  ; iso₂ = λ p → lem p _ }
  where
    iso₁ : (A B : HSet i)(p : A ≡ B)
         → unapΣ (ap proj₁ p , proj₁ (hn-h1 2 _ _ _)) ≡ p
    iso₁ (A , hA) .(A , hA) refl =
      ap (λ q → unapΣ (refl , q))
           (proj₁ (h↑ (hn-h1 2 A) hA hA _ refl))

    lem : ∀ {i j}{A : Set i}{B : A → Set j}
          {x x' : A}{y : B x}{y' : B x'}
          (p : x ≡ x')(q : subst B p y ≡ y')
        → ap proj₁ (unapΣ {B = B} (p , q)) ≡ p
    lem refl refl = refl

-- isomorphisms between hsets are automatically coherent
iso-coherence-h2 : ∀ {i}{A B : HSet i}
                 → (proj₁ A ≅' proj₁ B)
                 ≅ (proj₁ A ≅ proj₁ B)
iso-coherence-h2 {A = A , hA}{B = B , hB} =
  lem-contr (λ _ → Π-hlevel λ x → hB _ _ _ _)
  where
    lem-contr : ∀ {i j}{A : Set i}{B : A → Set j}
              → ((x : A) → contr (B x))
              → Σ A B ≅ A
    lem-contr cB = record
      { to = proj₁
      ; from = λ a → a , proj₁ (cB a)
      ; iso₁ = λ { (a , b) → unapΣ (refl , proj₂ (cB a) b) }
      ; iso₂ = λ _ → refl }

set-univ : ∀ {i} → univalent (set i)
set-univ {i} = λ A B →
  lem (≡⇒iso (set i) {A}{B})
      (lem-iso A B)
      (funext (lem-iso-comp A B))
  where
    open ≅-Reasoning

    -- the function corresponding to an isomorphism is a weak
    -- equivalence
    lem : ∀ {i j}{X : Set i}{Y : Set j}
          (f : X → Y)(isom : X ≅ Y)
        → (apply isom ≡ f)
        → weak-equiv f
    lem {X = X}{Y = Y} .(apply isom) isom refl =
      proj₂ (≅⇒≈ isom)

    -- equality in the category of sets is the same as isomorphism
    lem-iso : (A B : HSet i) → (A ≡ B) ≅ cat-iso (set i) A B
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
        cat-iso (set i) (A , hA) (B , hB)
      ∎

    -- the above isomorphism is given by ≡⇒iso
    lem-iso-comp : (A B : HSet i)(p : A ≡ B)
                 → apply (lem-iso A B) p
                 ≡ ≡⇒iso (set i) p
    lem-iso-comp A .A refl =
      ap₂ (c-iso (λ x → x) (λ x → x))
            (funext-id _) (funext-id _)
