{-# OPTIONS --without-K #-}

module category.graph.paths where

open import sum
open import level using (_⊔_)
open import equality.core hiding (singleton)
open import equality.calculus
open import equality.reasoning
open import sets.nat.core using (refl-≤)
open import hott.hlevel
open import category.graph.core

private
  module definition {i j}(W : Graph i j) where
    open as-graph W

    data Paths : obj W → obj W → Set (i ⊔ j) where
      nil : ∀ {x} → Paths x x
      _∷_ : ∀ {x y z}
          → hom x y
          → Paths y z
          → Paths x z
    infixr 5 _∷_
open definition public

private
  module hlevel {i j}{W : Graph i j}
                (hX : h 3 (obj W))
                (hW : h 2 (total W)) where
    open import decidable
    open import sum
    open import sets.empty
    open import sets.unit
    open import function.extensionality
    open import function.isomorphism
    open import container.core using (container)
    open import container.w renaming (W to W-type)
    open import hott.hlevel.closure.core

    X : Set i
    X = obj W

    I : Set i
    I = X × X

    A : I → Set _
    A (x , y) = (x ≡ y) ⊎ Σ (total W)
              λ { ((x' , y') , w) → (x' ≡ x) }

    A-hlevel : (i : I) → h 2 (A i)
    A-hlevel (x , y) = ⊎-hlevel refl-≤ (hX x y)
      (Σ-hlevel hW (λ { ((x' , _) , _) → hX x' x }))

    B : {i : I} → A i → Set _
    B {x , .x} (inj₁ refl) = ⊥
    B {.x , z} (inj₂ (((x , y) , w) , refl)) = ⊤

    r : {i : I}{a : A i} → B a → I
    r {x , .x} {inj₁ refl} ()
    r {.x , z} {inj₂ (((x , y) , w) , refl)} _ = y , z

    Paths' : X → X → Set _
    Paths' x y = W-type (container I A B r) (x , y)

    paths-iso : (x y : X) → Paths' x y ≅ Paths W x y
    paths-iso _ _ = iso f g iso₁ iso₂
      where
        f : {x y : X} → Paths' x y → Paths W x y
        f {x}{.x} (sup (inj₁ refl) _) = nil
        f {.x}{z} (sup (inj₂ (((x , y) , w) , refl)) u) = w ∷ f (u tt)

        g : {x y : X} → Paths W x y → Paths' x y
        g {x}{.x} nil = sup (inj₁ refl) (λ ())
        g {.x}{.z} (_∷_ {x}{y}{z} w ws) =
          sup (inj₂ (((x , y) , w) , refl)) (λ _ → g ws)

        iso₁ : {x y : X}(ws : Paths' x y) → g (f ws) ≡ ws
        iso₁ {x}{.x} (sup (inj₁ refl) _) = ap (sup (inj₁ refl)) (funext λ ())
        iso₁ {.x}{z} (sup (inj₂ (((x , y) , w) , refl)) u) =
          ap (sup (inj₂ (((x , y) , w) , refl))) (funext λ { tt → iso₁ (u tt) })

        iso₂ : {x y : X}(ws : Paths W x y) → f (g ws) ≡ ws
        iso₂ {x}{.x} nil = refl
        iso₂ (w ∷ ws) = ap (_∷_ w) (iso₂ ws)

    paths-hlevel : (x y : X) → h 2 (Paths W x y)
    paths-hlevel x y = iso-hlevel (paths-iso x y)
      (w-hlevel (λ { (x , y) → A-hlevel (x , y) }) (x , y))
open hlevel public using (paths-hlevel)

private
  module properties {i j}{W : Graph i j} where
    _++_ : ∀ {x y z} → Paths W x y → Paths W y z → Paths W x z
    nil ++ ws = ws
    (u ∷ us) ++ ws = u ∷ (us ++ ws)
    infixl 5 _++_

    ++-assoc : ∀ {x y z w}(ws : Paths W x y)(us : Paths W y z)(vs : Paths W z w)
          → ws ++ (us ++ vs)
          ≡ ws ++ us ++ vs
    ++-assoc nil us vs = refl
    ++-assoc (w ∷ ws) us vs = ap (λ α → w ∷ α) (++-assoc ws us vs)

    nil-right-unit : ∀ {x y} (ws : Paths W x y)
                      → ws ++ nil ≡ ws
    nil-right-unit nil = refl
    nil-right-unit (w ∷ ws) =
      ap (λ ws → w ∷ ws)
           (nil-right-unit ws)
open properties public
