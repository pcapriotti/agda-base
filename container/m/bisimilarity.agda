{-# OPTIONS --without-K #-}

module container.m.bisimilarity where

open import level
open import sum
open import equality.core
open import equality.calculus
open import equality.reasoning
open import function.core
open import container.core
open import container.equality
open import container.fixpoint
open import container.m.core
open import container.m.hlevel
open import hott.hlevel.core

private
  module Bisimilarity {li la lb}(c : Container li la lb) where
    open Definition c

    fp : Fixpoint c _
    fp = fix M fixpoint

    open Fixpoint fp
      using (head; tail)
    open Equality c fp
    module S = Definition equality

    _≡M_ : ∀ {i}(u v : M i) → Set _
    u ≡M v = S.M (_ , u , v)

    module Singl where
      c-singl : Container (li ⊔ la ⊔ lb) la lb
      c-singl = record
        { I = Σ I M
        ; A = λ {(i , u) → singleton (head u)}
        ; B = λ { {i , u} _ → B (head u)}
        ; r = λ { {i , u} b → _ , tail u b } }

      open Definition c-singl public

    Singl-M : ∀ {i} (u : M i) → Set _
    Singl-M {i} u = Singl.M (i , u)

    Singl-A-contr : ∀ i → contr (Singl.A i)
    Singl-A-contr (i , u) = singl-contr (head u)

    extract : ∀ {i}{u : M i} → Singl-M u → M i
    extract {u = inf .a h} (inf (a , refl) f) =
      inf a (λ b → ♯ extract (♭ (f b)))

    lift₁ : ∀ {i} (u : M i) → Singl-M u
    lift₁ (inf a f) = Singl.inf (a , refl) (λ b → ♯ lift₁ (♭ (f b)))

    lift₂ : ∀ {i}{u v : M i} → u ≡M v → Singl-M u
    lift₂ {i}{inf a f}{inf a' f'}(inf p h) =
      Singl.inf (a' , p) λ b → ♯ lift₂ (♭ (h b))

    section₁ : ∀ {i}(u : M i)
             → extract (lift₁ u) ≡ u
    section₁ u = unfold-η out (extract ∘ lift₁) (λ {(inf a f) → refl}) u
               ⊚ unfold-id u

    section₂ : ∀ {i}{u v : M i}(p : u ≡M v)
             → extract (lift₂ p) ≡ v
    section₂ {i}{u}{v} p = lem₂ p ⊚ sym (lem₁ p)
      where
        Eq : (i : I) → Set _
        Eq i = Σ (M i × M i) (uncurry _≡M_)

        α : Eq ↝ F Eq
        α {i} ((inf a f , inf .a f') , inf refl h) =
          a , λ b → (♭ (f b) , ♭ (f' b)) , ♭ (h b)

        f : ∀ {i}{u v : M i} → u ≡M v → M i
        f {i}{u}{v} p = unfold α ((u , v) , p)

        lem₁ : ∀ {i}{u v : M i}(p : u ≡M v) → v ≡ f p
        lem₁ {i}{u}{v} p = unfold-η α (λ {((_ , v) , _) → v})
                                      (λ {((inf a f , inf .a f') , inf refl h) → refl })
                                      ((u , v) , p)

        lem₂ : ∀ {i}{u v : M i}(p : u ≡M v) → extract (lift₂ p) ≡ f p
        lem₂ {i}{u}{v} p = unfold-η α (λ {(_ , p) → extract (lift₂ p)  })
                                      (λ {((inf a f , inf .a f') , inf refl h) → refl })
                                      ((u , v) , p)

    m-ext : ∀ {i}{u v : M i} → u ≡M v → u ≡ v
    m-ext {i}{u}{v} p = begin
        u
      ≡⟨ sym (section₁ u) ⟩
        extract (lift₁ u)
      ≡⟨ cong extract (contr⇒prop (m-contr Singl-A-contr (i , u)) _ _) ⟩
        extract (lift₂ p)
      ≡⟨ section₂ p ⟩
        v
      ∎
      where open ≡-Reasoning

open Bisimilarity public using (_≡M_; m-ext)
