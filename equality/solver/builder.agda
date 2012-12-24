{-# OPTIONS --without-K #-}
module equality.solver.builder {i}(X : Set i) where

open import level using (lzero)
open import decidable
open import sum
open import function.isomorphism
open import equality.core
open import equality.calculus
open import sets.fin using (Fin; zero; suc; _≟_)
open import sets.vec using (Vec; _!_; _∷_; [])

open import equality.solver.core
open import equality.solver.term

private
  transport-dec : ∀ {i j}{X : Set i}{Y : Set j}
                → X ≅ Y
                → ((x x' : X) → Dec (x ≡ x'))
                → ((y y' : Y) → Dec (y ≡ y'))
  transport-dec {Y = Y} isom dec = dec'
    where
      open _≅_ isom

      dec' : (y y' : Y) → Dec (y ≡ y')
      dec' y y' with dec (from y) (from y')
      ... | yes p = yes (sym (iso₂ y) ⊚ cong to p ⊚ iso₂ y')
      ... | no f = no (λ p → f (cong from p))

  module FinGraph {i}(X : Set i) where
    source : ∀ {n} → Vec (X × X) n → Fin n → X
    source v i = proj₁ (v ! i)

    target : ∀ {n} → Vec (X × X) n → Fin n → X
    target v i = proj₂ (v ! i)
    
    data fin-graph {n} (v : Vec (X × X) n) : Graph X lzero where
      fin-element : (i : Fin n) → fin-graph v (source v i) (target v i)

    element-index : ∀ {n x y}{v : Vec (X × X) n} → fin-graph v x y → Fin n
    element-index (fin-element i) = i

    total-space-finite : ∀ {n}(v : Vec (X × X) n)
                       → Fin n ≅ total-space (fin-graph v)
    total-space-finite {n} v = iso f g H K
      where
        E = total-space (fin-graph v)

        f : Fin n → E
        f i = (source v i , target v i) , fin-element i

        g : E → Fin n
        g (_ , w) = element-index w

        H : (i : Fin n) → g (f i) ≡ i
        H i = refl

        K : (e : E) → f (g e) ≡ e
        K ((.(source v i) , .(target v i)) , fin-element i) = refl

    fin-graph-dec : ∀ {n} (v : Vec (X × X) n)
                  → ((x y : X) → Dec (x ≡ y))
                  → DecGraph (fin-graph v)
    fin-graph-dec {n} v dec = dec-total dec (transport-dec (total-space-finite v) _≟_)
          
open FinGraph

make-term : ∀ {n x₀ y₀ x y}
          → ({W : Graph (Fin n) lzero} → Term W x₀ y₀ → Term W x y)
          → Term (fin-graph (Fin n) ((x₀ , y₀) ∷ [])) x y
make-term f = f (var (fin-element zero))

make-term₂ : ∀ {n x₀ y₀ x₁ y₁ x y}
          → ({W : Graph (Fin n) lzero} → Term W x₀ y₀ → Term W x₁ y₁ → Term W x y)
          → Term (fin-graph (Fin n) ((x₀ , y₀) ∷ (x₁ , y₁) ∷ [])) x y
make-term₂ f = f (var (fin-element zero)) (var (fin-element (suc zero)))

make-term₃ : ∀ {n x₀ y₀ x₁ y₁ x₂ y₂ x y}
          → ({W : Graph (Fin n) lzero} → Term W x₀ y₀ → Term W x₁ y₁ → Term W x₂ y₂ → Term W x y)
          → Term (fin-graph (Fin n) ((x₀ , y₀) ∷ (x₁ , y₁) ∷ (x₂ , y₂) ∷ [])) x y
make-term₃ f = f (var (fin-element zero)) (var (fin-element (suc zero))) (var (fin-element (suc (suc zero))))
