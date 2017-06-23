{-# OPTIONS --without-K #-}
module hott.truncation.elim where

open import sum
open import equality
open import function
open import hott.equivalence
open import hott.level
open import hott.loop
open import hott.truncation.core
open import hott.truncation.equality
open import hott.univalence
open import sets.nat
open import sets.unit

is-null : ∀ {i j}{X : Set i}{Y : Set j} → Y → (X → Y) → Set _
is-null y f = ∀ x → y ≡ f x

is-null-level : ∀ {i j}{X : Set i}{Y : Set j} → h 2 Y
              → (y : Y)(f : X → Y) → h 1 (is-null y f)
is-null-level hY y f = Π-level λ x → hY y (f x)

compose-is-null : ∀ {i j k}{X : Set i}{Y : Set j}{Z : Set k}
                → (y : Y)(f : X → Y)(g : Y → Z)
                → is-null y f
                → is-null (g y) (g ∘ f)
compose-is-null y f g c y' = ap g (c y')

Null : ∀ {i j} → ℕ → Set i → Set j → Set _
Null n X Y = Σ (X → Y) λ f → (x : X) → is-null (refl' n (f x)) (mapΩ n f)

-- connected components

Conn : ∀ {i}{X : Set i}(n : ℕ) → Trunc n X → Set _
Conn {X = X} n c = Σ X λ x → [ x ] ≡ c

map-conn : ∀ {i j}{X : Set i}{Y : Set j}(n : ℕ)
         → (c : Trunc n X)
         → (X → Y)
         → (Conn n c → Y)
map-conn n c f (x , p) = f x

conn-decomp : ∀ {i}{X : Set i}(n : ℕ)
            → Σ (Trunc n X) (Conn n) ≅ X
conn-decomp {X = X} n = total-iso [_]

conn-connected : ∀ {i}{X : Set i}(n : ℕ)(c : Trunc n X)
               → contr (Trunc n (Conn n c))
conn-connected {X = X} n c = φ c , lem c
  where
    φ' : (x : X) → Trunc n (Conn n [ x ])
    φ'  x = [ x , refl ]

    φ : (c : Trunc n X) → Trunc n (Conn n c)
    φ = Trunc-dep-elim n (λ c → Trunc n (Conn n c)) (λ _ → Trunc-level n) φ'

    lem' : (c : Trunc n X)(a : Conn n c) → φ c ≡ [ a ]
    lem' .([ x ]) (x , refl) = Trunc-dep-elim-β n
      (λ c → Trunc n (Conn n c))
      (λ _ → Trunc-level n) φ' x

    lem : (c : Trunc n X)(a : Trunc n (Conn n c)) → φ c ≡ a
    lem c = Trunc-dep-elim n (λ a → φ c ≡ a) (λ a → h↑ (Trunc-level n) (φ c) a) (lem' c)

-- main result

module CM {i j} n (X : Set i)(Y : Set j)
          (hY : h (n + 2) Y) where
  cm' : Y → Null n X Y
  cm' y = (λ _ → y) , (λ x p → sym (mapΩ-const n y x p))

  cm : (Trunc (suc n) X → Y) → Null n X Y
  cm f = (λ x → f [ x ]) , λ x
       → subst₂ (is-null) (mapΩ-refl n f) (eq x)
               (compose-is-null (refl' n [ x ]) (mapΩ n [_]) (mapΩ n f)
                 (λ p → h1⇒prop (Ω-level n hT) _ _))
     where
       f' : X → Y
       f' x = f [ x ]

       eq' : (x : X)(p : Ω n x) → mapΩ n f (mapΩ n [_] p) ≡ mapΩ n f' p
       eq' x p = mapΩ-hom n [_] f p

       eq : (x : X) → mapΩ n f ∘ mapΩ n [_] ≡ mapΩ n f'
       eq x = funext (eq' x)

       hT : h (n + 1) (Trunc (suc n) X)
       hT = subst (λ m → h m (Trunc (suc n) X)) (+-commutativity 1 n) (Trunc-level (suc n))

Trunc-elim' : ∀ {i j} n (X : Set i)(Y : Set j) → h (n + 2) Y
            → (Trunc (suc n) X → Y) ≅ Null n X Y

null-connected : ∀ {i j} n {X : Set i}{Y : Set j}
               → contr (Trunc (suc n) X)
               → h (n + 2) Y
               → (f : X → Y)
               → ((x : X) → is-null (refl' n (f x)) (mapΩ n f {x}))
               → (x : X) → is-null (f x) f
null-connected zero hX hY f c x₀ x₁ = c x₀ x₁
null-connected (suc n) {X} hX hY f c x₀ x₁
  = φ (trunc-equality (suc n) (h1⇒prop (h↑ hX) _ _))
  where
    ap-null : (x y : X)(p : x ≡ y) → is-null (refl' n (ap f p)) (mapΩ n (ap f) {p})
    ap-null x .x refl = c x

    φ : Trunc (suc n) (x₀ ≡ x₁) → f x₀ ≡ f x₁
    φ = invert (Trunc-elim' n (x₀ ≡ x₁) (f x₀ ≡ f x₁) (hY _ _))
        ( ap f , ap-null x₀ x₁ )

Trunc-elim-connected : ∀ {i j} n (X : Set i)(Y : Set j)
                     → contr (Trunc (suc n) X)
                     → h (n + 2) Y
                     → Y ≅ Null n X Y
Trunc-elim-connected n X Y hX hY = ≈⇒≅ (cm' , cm-equiv' (proj₁ hX))
  where
    open CM n X Y hY

    module _ (x₀ : X) where
      g : Null n X Y → Y
      g (f , c) = f x₀

      α : (y : Y) → g (cm' y) ≡ y
      α y = refl

      β : (x : Null n X Y) → cm' (g x) ≡ x
      β (f , c) = unapΣ ( (funext λ x → null-connected n hX hY f c _ _)
                        , h1⇒prop (Π-level λ x → is-null-level (Ω-level n hY) _ _) _ _)

      f-iso : Y ≅ Null n X Y
      f-iso = iso cm' g α β

    cm-equiv : X → weak-equiv cm'
    cm-equiv x₀ = proj₂ (≅⇒≈ (f-iso x₀))

    cm-equiv' : Trunc (suc n) X → weak-equiv cm'
    cm-equiv' = invert (Trunc-elim-iso (suc n) X (weak-equiv cm') (h! (weak-equiv-h1 cm'))) cm-equiv

abstract
  Trunc-elim'₀ : ∀ {i j} n (X : Set i)(Y : Set j) → h (n + 2) Y
              → (Trunc (suc n) X → Y) ≅ Null n X Y
  Trunc-elim'₀ n X Y hY = begin
      (Trunc (suc n) X → Y)
    ≅⟨ ( Π-ap-iso refl≅ λ c
       → Trunc-elim-connected n _ _ (conn-connected (suc n) c) hY) ⟩
      ((c : Trunc (suc n) X) → Null n (Conn (suc n) c) Y)
    ≅⟨ ΠΣ-swap-iso ⟩
      ( Σ ((c : Trunc (suc n) X) → Conn (suc n) c → Y) λ f
      → ((c : Trunc (suc n) X) → (x : Conn (suc n) c) → is-null _ (mapΩ n (f c))) )
    ≅⟨ sym≅ ( Σ-ap-iso (curry-iso (λ _ _ → Y)) λ f
            → curry-iso λ c x → is-null _ (mapΩ n (λ x' → f (c , x')))  ) ⟩
      ( Σ ((Σ (Trunc (suc n) X) λ c → Conn (suc n) c) → Y) λ f
      → (((x' : (Σ (Trunc (suc n) X) λ c → Conn (suc n) c))
           → is-null _ (mapΩ n (λ x → f (proj₁ x' , x))))) )
    ≅⟨ ( Σ-ap-iso' (→-ap-iso (conn-decomp (suc n)) refl≅) λ f
       → Π-ap-iso (conn-decomp (suc n)) λ x → refl≅ ) ⟩
      ( Σ (X → Y) λ f
      → (((x : X) → is-null _ (mapΩ n (λ x → f (proj₁ x)) {x , refl}))) )
    ≅⟨ ( Σ-ap-iso refl≅ λ f → Π-ap-iso refl≅ λ x → lem f x ) ⟩
      Null n X Y
    ∎
    where
      open ≅-Reasoning

      lem : (f : X → Y) (x : X)
          → is-null (refl' n (f x)) (mapΩ n (map-conn (suc n) [ x ] f) {x , refl})
          ≅ is-null (refl' n (f x)) (mapΩ n f {x})
      lem f x = ≡⇒≅ (ap (is-null (refl' n (f x))) (funext hom)) ·≅ sym≅ is-const-equiv
        where
          π : Conn (suc n) [ x ] → X
          π = proj₁

          hom : (p : Ω n (x , refl))
              → mapΩ n (map-conn (suc n) [ x ] f) p
              ≡ mapΩ n f (mapΩ n proj₁ p)
          hom p = sym (mapΩ-hom n proj₁ f p)

          φ : Ω n {Conn (suc n) [ x ]} (x , refl) ≅ Ω n x
          φ = loop-sum n λ a → Trunc-level (suc n) _ _

          is-const-equiv : is-null {X = Ω n x} (refl' n (f x)) (mapΩ n f {x})
                         ≅ is-null {X = Ω n {Conn (suc n) [ x ]} (x , refl)}
                                   (refl' n (f x))
                                   (mapΩ n f ∘ mapΩ n proj₁)
          is-const-equiv = Π-ap-iso (sym≅ φ) λ p
                         → refl≅

  Trunc-elim'-β₀ : ∀ {i j n}{X : Set i}{Y : Set j} (hY : h (n + 2) Y)
                → (f : Trunc (suc n) X → Y)
                → proj₁ (apply (Trunc-elim'₀ n X Y hY) f) ≡ (λ x → f [ x ])
  Trunc-elim'-β₀ hY f = refl

  Trunc-elim'-β : ∀ {i j n}{X : Set i}{Y : Set j} (hY : h (n + 2) Y)
                → (f : Trunc (suc n) X → Y)
                → apply (Trunc-elim'₀ n X Y hY) f ≡ CM.cm n X Y hY f
  Trunc-elim'-β {n = n} hY f = unapΣ
    ( Trunc-elim'-β₀ hY f
    , h1⇒prop (Π-level λ x → is-null-level (Ω-level n hY) _ _) _ _ )

Trunc-elim' n X Y hY = ≈⇒≅ (cm , cm-we)
  where
    open CM n X Y hY

    cm-eq : apply (Trunc-elim'₀ n X Y hY) ≡ cm
    cm-eq = funext (Trunc-elim'-β hY)

    cm-we : weak-equiv cm
    cm-we = subst weak-equiv cm-eq (proj₂ (≅⇒≈ (Trunc-elim'₀ n X Y hY)))

-- example

Repr : ∀ {i} → Set i → Set _
Repr {i} A = Σ (Trunc 2 A → Set i) λ hom
       → (a : A) → hom [ a ] ≅ (a ≡ a)

Braiding : ∀ {i} → Set i → Set _
Braiding A = {a : A}(p q : a ≡ a) → p · q ≡ q · p

braiding-repr : ∀ {i}{A : Set i} → h 3 A → Braiding A → Repr A
braiding-repr {i}{A} hA γ = (λ c → proj₁ (hom c)) , λ a
                          → ≡⇒≅ (ap proj₁ (hom-β a))
  where
    eq : A → Set _
    eq a = (a ≡ a)

    hom' : A → Type _ 2
    hom' a = eq a , hA a a

    type-eq-iso : ∀ {n}{X Y : Type i n}
                → (X ≡ Y) ≅ (proj₁ X ≈ proj₁ Y)
    type-eq-iso {n}{X}{Y} = begin
        (X ≡ Y)
      ≅⟨ sym≅ Σ-split-iso ⟩
        (Σ (proj₁ X ≡ proj₁ Y) λ p → subst (h n) p (proj₂ X) ≡ proj₂ Y)
      ≅⟨ (Σ-ap-iso refl≅ λ p → contr-⊤-iso (hn-h1 n _ _ _)) ⟩
        ((proj₁ X ≡ proj₁ Y) × ⊤)
      ≅⟨ ×-right-unit ⟩
        (proj₁ X ≡ proj₁ Y)
      ≅⟨ uni-iso ⟩
        (proj₁ X ≈ proj₁ Y)
      ∎
      where open ≅-Reasoning

    type-eq : ∀ {n}{X : Type i n}{p : X ≡ X}
            → ((x : proj₁ X) → coerce (ap proj₁ p) x ≡ x)
            → p ≡ refl
    type-eq f = invert≅ (iso≡ type-eq-iso) (unapΣ
              ( funext f , h1⇒prop (weak-equiv-h1 _) _ _))

    ap-eq : {a b : A}(p : a ≡ b)(q : a ≡ a) → coerce (ap proj₁ (ap hom' p)) q ≡ sym p · q · p
    ap-eq refl q = sym (left-unit q)

    hom-null : (a : A) → is-null refl (mapΩ 1 hom' {a})
    hom-null a p = sym (type-eq λ q → ap-eq p q
                                    · ap (λ z → z · p) (γ (sym p) q)
                                    · associativity q (sym p) p
                                    · ap (λ z → q · z) (right-inverse p)
                                    · left-unit q)

    hom-iso : (Trunc 2 A → Type i 2) ≅ Null 1 A (Type i 2)
    hom-iso = Trunc-elim' 1 A (Type i 2) type-level

    hom : Trunc 2 A → Type _ 2
    hom = invert hom-iso (hom' , hom-null)

    hom-β : (a : A) → hom [ a ] ≡ hom' a
    hom-β a = funext-inv (ap proj₁ (_≅_.iso₂ hom-iso (hom' , hom-null))) a
