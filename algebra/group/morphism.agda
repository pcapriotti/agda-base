{-# OPTIONS --without-K #-}

module algebra.group.morphism where

open import level
open import algebra.group.core

import algebra.monoid.morphism as Mon

open Group

Morphism : ∀ {i j} → Group i → Group j → Set (i ⊔ j)
Morphism A B = Mon.Morphism (mon A) (mon B)
