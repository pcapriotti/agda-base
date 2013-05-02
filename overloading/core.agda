{-# OPTIONS --without-K #-}
module overloading.core where

-- ## Coercions
--
-- The overloading system implemented in this module is based on
-- **coercions**. A coercion is simply a function converting a type into
-- another. In object-oriented parliance, a coercion embodies an *is-a*
-- relationship.  The two types involved in a coercions are called `Source` and
-- `Target` respectively, and the coercion itself is a function `Source →
-- Target`.
--
-- Coercions are implemented as terms of type `Coercion`, which is a record
-- parameterized over the `Source` and `Target` types, with a single field for
-- the actual coercion function.  Of course, the type `Coercion X Y` is
-- isomorphic to `X → Y`, but using a record prevents possible ambiguities when
-- using coercions as implicit parameters, and potentially makes instance
-- resolution faster.
--
-- The typical scenario where coercions are used is when defining a subtype
-- relationships between types.  Although Agda has no built-in support for
-- subtypes, it is possible to achieve a reasonable level of syntactical
-- convenience with the help of some boilerplace code that specifies the
-- subtyping relation explicitly.  See `category.graph.core` for a detailed
-- example.
--
-- This module also contains some functions to help reduce the amount of
-- boilerplate needed for defining all the coercions necessary for a given type.
-- See `coerce-self` and `coerce-parent` below.
--
-- ## Methods
--
-- The strategy employed by this library to implement overloading goes as
-- follows.  Every type (denoted by `Target` in the following) defines a set of
-- "methods" that constitute its interface, and are inherited by every subtype
-- of `Target`.  Methods are divided into 2 groups:
--
-- - **static methods** are functions that take an argument `X` of a type
-- convertible to `Target`. The typical example of a static method is an
-- explicit coercion function, like `∣_∣` below, which returns the "underlying
-- set" of `X`.  Another example of static method is the `total` function for
-- graphs (see `category.graph.core`).
--
-- - **instance methods** are functions that work without requiring an explicit
-- parameter of type `Target`.  A typical example of instance method is
-- composition in a category (`_∘_`): there's no need to pass the category
-- itself when composing two morphisms.  In order to use instance methods, they
-- have to be enabled explicitly for each instance for which they are used.
-- Every type defines a special module (whose name is by convention always
-- `as-target`, where `target` is replaced with the actual lowercase name of
-- type) which allows instance methods to be enabled.  For example, to use the
-- composition operator for morphisms of a category `C`, one can write:
--
--    open as-category C
--
-- The `as-target` module itself behaves like a *static* method, so it can be
-- used to enable instance methods for any superclass of a given instance.
-- Furthermore, enabling instance methods for `Target` enables instance methods
-- for all superclasses of it in its principal inheritance path (see
-- "Inheritance Model" below).
--
-- ## Implementation
--
-- The implementation of static methods is relatively straightforward.  A static
-- method is defined as a function taking a coercion to `Target` as an instance
-- argument, and uses the coercion to convert its argument to the correct type.
--
-- As for instance methods, they are implemented as functions that take a record
-- with the full interface of `Target` (called **instance record** below) as an
-- implicit argument (see "Alternative Notations" below for details), and just
-- return the appropriate field.  This can be accomplished very easily using
-- Agda's module system.
--
-- The `as-target` module, used to enable instance methods, is defined as a
-- static method, and works simply by putting the record above into scope.
--
-- ## Alternative Notations
--
-- Some types have an interface which supports alternative notations.  For
-- example, monoids have a "default" notation (`unit` and `_*_`), and an
-- additive notation (`zero` and `_+_`).
--
-- To implement multiple notations, a `Styled` record is used as the implicit
-- parameter for instance methods.  The `Styled` record is parameterized over a
-- `style` parameter (normally `default`), and contains the interface record as
-- its only field.
--
-- The `Styled` record thus serves two purposes:
--
-- - It prevents ambiguities in the resolution of instance arguments: if an
-- interface record is in scope for reasons unrelated to the overloading system,
-- then it will not be accidentally used as the argument of an instance methods,
-- as it's not wrapped in a `Styled` record.
--
-- - It allows instance methods to specify an alternative style parameter for
-- the record in which the interface record is wrapped.  Thus, multiple
-- `as-target` module can be defined, one per supported style, that put the
-- interface record in scope wrapped in the appropriate `Styled` record.  The
-- `styled` function can be used to wrap an interface record using a given
-- style.
--
-- ## Inheritance Model
--
-- Subtyping relations can form an arbitrary directed graph, with a
-- distinguished spanning forest, whose edges we call *principal*.
--
-- Coercions are defined for every pair of connected nodes in the full graph.
-- Exactly one coercion per pair should be defined, regardless of the number of
-- paths that connect it.  Static methods are inherited automatically through
-- paths in the full DAG, since the existence of a coercion is enough for static
-- methods to propagate.
--
-- The principal subgraph is used for inheritance instance methods.  Namely, the
-- `as-target` record enables all instance methods for the ancestors of `Target`
-- in the principal subgraph.  This is accomplished by simply re-exporting the
-- `as-target` module for the immediate parent of `Target`. Extra edges coming
-- out of `Target` can optionally be added as well for convenience.

open import level
open import overloading.bundle

record Coercion {i}{j}(Source : Set i)(Target : Set j) : Set (i ⊔ j) where
  constructor coercion
  field
    coerce : Source → Target
open Coercion public

data Style : Set where default : Style

record Styled {i}(style : Style)(X : Set i) : Set i where
  field value : X

styled : ∀ {i}{X : Set i} → (s : Style) → X → Styled s X
styled s x = record { value = x }

-- Trivial coercion: any type can be coerced into itself.
coerce-self : ∀ {i} (X : Set i) → Coercion X X
coerce-self {i} _ = record
  { coerce = λ x → x }

-- Transport a coercion to a `Bundle` subtype.  See `overloading.bundle` for
-- more details on bundles.
coerce-parent : ∀ {i j k}
                {X : Set i}
                {Y : Set j}
              → ⦃ c : Coercion X Y ⦄
              → {Struct : X → Set k}
              → Coercion (Bundle Struct) Y
coerce-parent ⦃ c ⦄ = record
  { coerce = λ x → coerce c (Bundle.parent x) }

set-is-set : ∀ {i} → Coercion (Set i) (Set i)
set-is-set {i} = coerce-self _

∣_∣ : ∀ {i j}{Source : Set i} ⦃ o : Coercion Source (Set j) ⦄
    → Source → Set j
∣_∣ ⦃ c ⦄ = coerce c
