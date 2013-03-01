{-# OPTIONS --without-K #-}
module solver.equality.builder where

open import level using (lzero; lsuc; _⊔_)
open import decidable
open import sum
open import function
open import function.isomorphism
open import equality.core
open import equality.calculus
open import sets.fin using (Fin; zero; suc; _≟_)
open import sets.vec using (Vec; _!_; _∷_; []; lookup)

open import solver.equality.core
open import solver.equality.term

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

  module FinEdges {i}(X : Set i) where
    source : ∀ {n} → Vec (X × X) n → Fin n → X
    source v i = proj₁ (v ! i)

    target : ∀ {n} → Vec (X × X) n → Fin n → X
    target v i = proj₂ (v ! i)
    
    data fin-graph {n} (v : Vec (X × X) n) : Edges X lzero where
      fin-element : (i : Fin n) → fin-graph v (source v i) (target v i)

    total-space-finite : ∀ {n}(v : Vec (X × X) n)
                       → Fin n ≅ total-space (fin-graph v)
    total-space-finite {n} v = iso f g H K
      where
        E = total-space (fin-graph v)

        f : Fin n → E
        f i = (source v i , target v i) , fin-element i

        g : E → Fin n
        g ((.(source v i) , .(target v i)) , fin-element i) = i

        H : (i : Fin n) → g (f i) ≡ i
        H i = refl

        K : (e : E) → f (g e) ≡ e
        K ((.(source v i) , .(target v i)) , fin-element i) = refl
        
    fin-graph-dec : ∀ {n} (v : Vec (X × X) n)
                  → ((x y : X) → Dec (x ≡ y))
                  → DecGraph (fin-graph v)
    fin-graph-dec {n} v dec = dec-total dec (transport-dec (total-space-finite v) _≟_)

open FinEdges public

fin-env : ∀ {i k n}{X : Set i}(v : Vec (Fin k × Fin k) n)(xs : Vec X k)
        → ((i : Fin n) → xs ! proj₁ (v ! i) ≡ xs ! proj₂ (v ! i))
        → Env (fin-graph (Fin k) v) X
fin-env {k = k}{X = X} v xs f = record
  { imap = lookup xs
  ; gmap = lookup' v f }
  where
    lookup' : ∀ {n}(v : Vec (Fin k × Fin k) n)
            → ((i : Fin n) → xs ! proj₁ (v ! i) ≡ xs ! proj₂ (v ! i))
            → ∀ {i j} → fin-graph (Fin k) v i j → (xs ! i) ≡ (xs ! j)
    lookup' [] f (fin-element ())
    lookup' ((i , j) ∷ v) f (fin-element zero) = f zero
    lookup' ((i , j) ∷ v) f (fin-element (suc n)) = lookup' v (f ∘ suc) (fin-element n)

HOTerm' : ∀ {i n} {X : Set i} → Edges X lzero → Vec (X × X) n → X → X → Set i
HOTerm' W [] x y = Term W x y
HOTerm' W ((x' , y') ∷ v) x y = Term W x' y' → HOTerm' W v x y

HOTerm : ∀ {i n} → (X : Set i) → Vec (X × X) n → X → X → Set (lsuc lzero ⊔ i)
HOTerm X v x y = {W : Edges X lzero} → HOTerm' W v x y

term : ∀ {n k} {v : Vec (Fin n × Fin n) k}{x y : Fin n}
     → HOTerm (Fin n) v x y
     → Term (fin-graph (Fin n) v) x y
term {v = v}{x}{y} t = go v x y t (var ∘ fin-element)
  where
    go : ∀ {i n}{X : Set i}{W : Edges X lzero}(v : Vec (X × X) n)(x y : X)
       → HOTerm' W v x y
       → ((i : Fin n) → Term W (proj₁ (v ! i)) (proj₂ (v ! i)))
       → Term W x y
    go [] x y t _ = t
    go ((x' , y') ∷ v) x y f e = go v x y (f (e zero)) (e ∘ suc)
