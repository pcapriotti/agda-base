# agda-base

[![build status](https://gitlab.com/pcapriotti/agda-base/badges/master/build.svg)](https://gitlab.com/pcapriotti/agda-base/commits/master)

This is a self-contained repository of basic results and utilities for
Homotopy Type Theory.

Modules are structured in a hierarchy, where all top-level modules are
imported in this file, and each module only imports and re-exports all
sub-modules. The most basic definitions for a submodule collection are
defined in the `core` submodule.

For example, in the case of equality, the module called `equality` is
composed of a number of submodules: `core` (containing the basic
definitions), `groupoid` (groupoid laws), `calculus` (for calculations
involving equality proofs) and `reasoning` (for equational reasoning).
