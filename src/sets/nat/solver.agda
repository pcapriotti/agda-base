module sets.nat.solver where

open import decidable
open import equality
open import function.core
  hiding (const)
open import sets.nat.core
open import sets.nat.properties
open import sets.nat.ordering
open import sets.fin.core
  hiding (_≟_)
open import sets.vec.core
open import sets.vec.dependent

data Exp (n : ℕ) : Set where
  var : Fin n → Exp n
  const : ℕ → Exp n
  _:+_ : Exp n → Exp n → Exp n
infixl 6 _:+_

eval : ∀ {n} → (Fin n → ℕ) → Exp n → ℕ
eval env (var i) = env i
eval env (const x) = x
eval env (e₁ :+ e₂) = eval env e₁ + eval env e₂

NF : ℕ → Set
NF n = Vec ℕ n

evalNF' : ∀ {n} → (Fin n → ℕ) → NF n → ℕ
evalNF' _ [] = 0
evalNF' env (x ∷ xs) = x * env zero + evalNF' (env ∘' suc) xs

evalNF : ∀ {n} → (Fin n → ℕ) → NF (suc n) → ℕ
evalNF env xs = evalNF' (1 ∷∷ env) xs

decNF : ∀ {n}(xs ys : NF n) → Dec (xs ≡ ys)
decNF [] [] = yes refl
decNF (x ∷ xs) (y ∷ ys) with x ≟ y | decNF xs ys
decNF (x ∷ xs) (y ∷ ys) | _ | no u = no λ p → u (ap tail p)
decNF (x ∷ xs) (y ∷ ys) | no u | _ = no λ p → u (ap head p)
decNF (x ∷ xs) (y ∷ ys) | yes p | yes q = yes (ap₂ _∷_ p q)

emptyNF : ∀ {n} → NF n
emptyNF {zero} = []
emptyNF {suc n} = 0 ∷ emptyNF

eval-emptyNF : ∀ {n}(env : Fin n → ℕ) → evalNF' env emptyNF ≡ 0
eval-emptyNF {zero} env = refl
eval-emptyNF {suc n} env = eval-emptyNF {n} (env ∘' suc)

δ : ∀ {n} → Fin n → ℕ → NF n
δ zero val = val ∷ emptyNF
δ (suc i) val = 0 ∷ δ i val

eval-δ : ∀ {n}(i : Fin n)(val : ℕ)
       → (env : Fin n → ℕ)
       → evalNF' env (δ i val) ≡ val * env i
eval-δ zero val env = ap (_+_ (val * env zero)) (eval-emptyNF env)
                    · +-right-unit _
eval-δ (suc i) val env = eval-δ i val (env ∘' suc)

_+NF_ : ∀ {n} → NF n → NF n → NF n
[] +NF [] = []
(x ∷ xs) +NF (y ∷ ys) = (x + y) ∷ (xs +NF ys)

eval+NF : ∀ {n}(xs ys : NF n)(env : Fin n → ℕ)
        → evalNF' env (xs +NF ys)
        ≡ evalNF' env xs + evalNF' env ys
eval+NF [] [] env = refl
eval+NF (x ∷ xs) (y ∷ ys) env
  = ap₂ _+_ (right-distr x y (env zero)) (eval+NF xs ys (env ∘' suc))
  · lem (x * env zero) (y * env zero) (evalNF' (env ∘' suc) xs) (evalNF' (env ∘' suc) ys)
  where
    lem : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    lem a b c d
      = +-associativity a b (c + d)
      · ap (_+_ a) (sym (+-associativity b c d))
      · ap (λ z → a + (z + d)) (+-commutativity b c)
      · ap (_+_ a) (+-associativity c b d)
      · sym (+-associativity a c (b + d))

nf : ∀ {n} → Exp n → NF (suc n)
nf (var i) = δ (suc i) 1
nf (const k) = δ zero k
nf (e₁ :+ e₂) = nf e₁ +NF nf e₂

nf-sound : ∀ {n}(env : Fin n → ℕ)(e : Exp n)
         → evalNF env (nf e) ≡ eval env e
nf-sound env (var i) = eval-δ i 1 env · +-right-unit (env i)
nf-sound env (const x) = ap (_+_ (x * 1)) (eval-emptyNF env)
                       · +-right-unit (x * 1)
                       · *-right-unit x
nf-sound env (e₁ :+ e₂) = eval+NF (nf e₁) (nf e₂) (1 ∷∷ env)
                        · ap₂ _+_ (nf-sound env e₁) (nf-sound env e₂)

HOTerm : ℕ → ℕ → Set
HOTerm n zero = Exp n
HOTerm n (suc i) = Exp n → HOTerm n i

private
  exp' : (n i : ℕ) → i ≤ n → HOTerm n i → (Fin i → Exp n) → Exp n
  exp' _ zero _ e _ = e
  exp' zero (suc i) () e f
  exp' (suc n) (suc i) p e f = exp' (suc n) i (trans≤ suc≤ p) (e (f zero)) (f ∘' suc)

exp : ∀ {n} → HOTerm n n → Exp n
exp {n} e = exp' n n refl≤ e var

solve : ∀ n (e₁ e₂ : Exp n){t : True (decNF (nf e₁) (nf e₂))}
      → (env : Fin n → ℕ)
      → eval env e₁ ≡ eval env e₂
solve n e₁ e₂ {t} env = sym (nf-sound env e₁)
                      · ap (evalNF env) (witness t)
                      · nf-sound env e₂
