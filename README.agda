{-# OPTIONS --without-K #-}
module README where

-- This is a self-contained repository of basic results and utilities for
-- Homotopy Type Theory.
--
-- Modules are structured in a hierarchy, where all top-level modules are
-- imported in this file, and each module only imports and re-exports all
-- sub-modules. The most basic definitions for a submodule collection are
-- defined in the `core` submodule.
--
-- For example, in the case of equality, the module called `equality` is
-- composed of a number of submodules: `core` (containing the basic
-- definitions), `groupoid` (groupoid laws), `calculus` (for calculations
-- involving equality proofs) and `reasoning` (for equational reasoning).

-- Σ types and related utilities
import sum

-- Propositional equality
import equality

-- Basic types
import sets

-- Decidable predicates
import decidable

-- Functions, isomorphisms and properties thereof
import function

-- Universe levels
import level

-- Container functors, W and M types
import container

-- Solvers: automate certain kinds of proofs
import solver

-- Category theory
import category

-- Basic algebra
import algebra

-- Homotopy type theory infrastructure and results
import hott

-- Higher Inductive Types
import higher
