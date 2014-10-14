module container.w where

open import level
open import sum
open import equality
open import function.extensionality
open import function.isomorphism
open import function.isomorphism.properties
open import function.overloading
open import sets.empty
open import sets.nat.core using (suc)
open import sets.unit
open import hott.level
open import container.core
open import container.fixpoint
open import container.equality

private
  module Definition {li la lb} (c : Container li la lb) where
    open Container c

    -- definition of indexed W-types using a type family
    data W (i : I) : Set (li ⊔ la ⊔ lb) where
      sup : (a : A i) → (∀ j → B a j → W j) → W i

    -- initial F-algebra
    inW : F W ↝ W
    inW (a , f) = sup a f

    module Elim {lx} {X : I → Set lx}
                (α : F X ↝ X) where
      -- catamorphisms
      fold : W ↝ X
      fold (sup a f) = α (a , λ j b → fold (f j b))

      -- computational rule for catamorphisms
      -- this holds definitionally
      fold-β : ∀ {i} (x : F W i) → fold (inW x) ≡ α (imap W fold x)
      fold-β x = refl

      -- η-rule, this is only propositional
      fold-η : (h : W ↝ X)
             → (∀ {i} (x : F W i) → h (inW x) ≡ α (imap W h x))
             → ∀ {i} (x : W i) → h x ≡ fold x
      fold-η h p {i} (sup a f) = p (a , λ b → f b) · lem
        where
          lem : α (a , (λ j b → h (f j b)))
              ≡ α (a , (λ j b → fold (f j b)))
          lem = ap (λ h → α (a , h))
                   (funext λ i → funext λ b → fold-η h p (f i b))
    open Elim public

    head : ∀ {i} → W i → A i
    head (sup a f) = a

    tail : ∀ {i} (x : W i) → ∀ j → B (head x) j → W j
    tail (sup a f) = f

    fixpoint : (i : I) → W i ≅ F W i
    fixpoint _ = iso f g H K
      where
        f : {i : I} → W i → F W i
        f (sup a f) = a , f

        g : {i : I} → F W i → W i
        g (a , f) = sup a f

        H : {i : I}(w : W i) → g (f w) ≡ w
        H (sup a f) = refl

        K : {i : I}(w : F W i) → f (g w) ≡ w
        K (a , f) = refl

private
  module Properties {li la lb}{c : Container li la lb} where
    open Container c
    open Definition c

    open Equality c (fix W fixpoint)
    open Container equality
      using ()
      renaming ( F to F-≡' )
    open Definition equality
      using ()
      renaming ( W to W-≡
               ; fixpoint to fixpoint-≡ )

    F-≡ : ∀ {lx}
        → (∀ {i} → W i → W i → Set lx)
        → (∀ {i} → W i → W i → Set _)
    F-≡ X  u v = F-≡' (λ {(i , u , v) → X {i} u v}) (_ , u , v)

    _≡W_ : ∀ {i} → W i → W i → Set _
    _≡W_ {i} u v = W-≡ (i , u , v)

    fixpoint-W : ∀ {i}{u v : W i} → (u ≡ v) ≅ F-≡ _≡_ u v
    fixpoint-W {i}{sup a f}{sup a' f'} = begin
        (sup a f ≡ sup a' f')
      ≅⟨ iso≡ (fixpoint i) ⟩
        (_≡_ { A = F W i } (a , f) (a' , f'))
      ≅⟨ sym≅ Σ-split-iso ⟩
        ( Σ (a ≡ a') λ p → subst (λ a → (j : I) → B a j → W j) p f ≡ f' )
      ≅⟨ ( Σ-ap-iso refl≅ λ p → lem p f f' ) ⟩
        ( Σ (a ≡ a') λ p → f ≡ (λ j b → f' j (σ p b)) )
      ≅⟨ (Σ-ap-iso refl≅ λ p → sym≅ strong-funext-iso) ⟩
        ( Σ (a ≡ a') λ p → ∀ j → f j ≡ λ b → f' j (σ p b) )
      ≅⟨ (Σ-ap-iso refl≅ λ p → Π-ap-iso refl≅ λ j → sym≅ strong-funext-iso) ⟩
        ( Σ (a ≡ a') λ p → ∀ j (b : B a j) → f j b ≡ f' j (σ p b) )
      ≅⟨ ( Σ-ap-iso refl≅ λ p
         → Π-ap-iso refl≅ λ j
         → Π-ap-iso refl≅ λ b
         → J-iso ) ⟩
        ( Σ (a ≡ a') λ p → ∀ j (b : B a j)
        → (x' : W j) → f j b ≡ x'
        → x' ≡ f' j (σ p b) )
      ≅⟨ ( Σ-ap-iso refl≅ λ p
         → Π-ap-iso refl≅ λ j
         → Π-ap-iso refl≅ λ b
         → Π-ap-iso refl≅ λ x'
         → Π-ap-iso refl≅ λ _
         → J-iso ) ⟩
        ( Σ (a ≡ a') λ p → ∀ j → (b : B a j)
        → (x' : W j) → f j b ≡ x'
        → (y' : W j) → f' j (σ p b) ≡ y'
        → x' ≡ y' )
      ≅⟨ lem' ⟩
        ( Σ (a ≡ a') λ p → ∀ j' → let (j , x' , y') = j'
        in B-≡ {i , sup a f , sup a' f'} p j' → x' ≡ y' )
      ∎
      where
        open ≅-Reasoning

        σ : a ≡ a' → ∀ {j} → B a j → B a' j
        σ p {j} = subst (λ a → B a j) p

        lem : ∀ {a a' : A i} (p : a ≡ a')
            → (f : ∀ j → B a j → W j)
            → (f' : ∀ j → B a' j → W j)
            → (subst (λ a → ∀ j → B a j → W j) p f ≡ f')
            ≅ (f ≡ (λ j b → f' j (subst (λ a → B a j) p b)))
        lem refl f f' = refl≅

        lem' : ( Σ (a ≡ a') λ p → ∀ j → (b : B a j)
               → (x' : W j) → f j b ≡ x'
               → (y' : W j) → f' j (σ p b) ≡ y'
               → x' ≡ y' )
             ≅ ( Σ (a ≡ a') λ p → ∀ j' → let (j , x' , y') = j'
               in B-≡ {i , sup a f , sup a' f'} p j' → x' ≡ y' )
        lem' = record
          { to = λ { (p , u) → p , (λ { (j , x' , y') (b , q , r)
                   → u j b x' q y' r }) }
          ; from = λ { (p , u) → p , λ j b x' q y' r → u (j , x' , y') (b , q , r) }
          ; iso₁ = λ { (p , u) → refl }
          ; iso₂ = λ { (p , u) → refl } }

    str-iso : ∀ {i}{u v : W i} → (u ≡ v) ≅ (u ≡W v)
    str-iso {i}{sup a f}{sup a' f'} = begin
        (sup a f ≡ sup a' f')
      ≅⟨ fixpoint-W ⟩
        F-≡ _≡_ (sup a f) (sup a' f')
      ≅⟨ ( Σ-ap-iso refl≅ λ p
         → Π-ap-iso refl≅ λ { (j , x' , y')
         → Π-ap-iso refl≅ λ { (b , q , r)
         → lem f f' p j x' y' b q r str-iso }} ) ⟩
        F-≡ _≡W_ (sup a f) (sup a' f')
      ≅⟨ sym≅ (fixpoint-≡ _) ⟩
        (sup a f ≡W sup a' f')
      ∎
      where
        lem : {a a' : A i}(f : ∀ j → B a j → W j)(f' : ∀ j → B a' j → W j)
            → (p : a ≡ a')(j : I)(x' y' : W j)(b : B a j)
            → (q : f j b ≡ x')(r : f' j (subst (λ a → B a j) p b) ≡ y')
            → ((f j b ≡ f' j (subst (λ a → B a j) p b)) ≅ (f j b ≡W f' j (subst (λ a → B a j) p b)))
            → ((x' ≡ y') ≅ (x' ≡W y'))
        lem f f' refl j ._ ._ b refl refl isom = isom
        open ≅-Reasoning

    w-level : ∀ {n} → ((i : I) → h (suc n) (A i)) → (i : I) → h (suc n) (W i)
    w-level {n} hA i (sup a f) (sup a' f') = iso-level (sym≅ fixpoint-W)
      ( Σ-level (hA i a a') λ p → Π-level λ { (j , x' , y')
      → Π-level λ { (b , q , r)
      → lem f f' p j x' y' b q r (w-level hA j (f j b) (f' j (subst (λ a → B a j) p b))) } } )
      where
        lem : ∀ {i}{a a' : A i}
              (f : ∀ j → (b : B a j) → W j)
              (f' : ∀ j → (b : B a' j) → W j)
            → (p : a ≡ a')(j : I)(x' y' : W j)
            → (b : B a j)(q : f j b ≡ x')(r : f' j (subst (λ a → B a j) p b) ≡ y')
            → h n (f j b ≡ f' j (subst (λ a → B a j) p b))
            → h n (x' ≡ y')
        lem f f' refl j ._ ._ b refl refl h' = h'

open Definition public
open Properties public using (w-level)
