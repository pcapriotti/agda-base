{-# OPTIONS --without-K #-}
module sets.vec.properties where

open import equality.core
open import function.core
open import function.extensionality
open import function.isomorphism
open import sets.nat.core using (ℕ; zero; suc)
open import sets.fin using (Fin; zero; suc)
open import sets.vec.core

tabulate-lookup : {A : Set}{n : ℕ}
                → (xs : Vec A n)
                → tabulate (lookup xs) ≡ xs
tabulate-lookup [] = refl
tabulate-lookup (x ∷ xs) = ap (_∷_ x) (tabulate-lookup xs)

lookup-tabulate-funext : {A : Set}{n : ℕ}
                    → (f : Fin n → A)(i : Fin n)
                    → lookup (tabulate f) i ≡ f i
lookup-tabulate-funext {n = zero} f ()
lookup-tabulate-funext {n = suc m} f zero = refl
lookup-tabulate-funext {n = suc m} f (suc i) =
  lookup-tabulate-funext (f ∘ suc) i

lookup-tabulate : {A : Set}{n : ℕ}
                → (f : Fin n → A)
                → lookup (tabulate f) ≡ f
lookup-tabulate f = funext (lookup-tabulate-funext f)

lookup-iso : {A : Set}{n : ℕ}
           → Vec A n ≅ (Fin n → A)
lookup-iso = iso lookup tabulate tabulate-lookup lookup-tabulate
