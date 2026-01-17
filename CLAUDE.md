# Project Guidelines

## Overview

**tamagoh** is a Haskell implementation of e-graphs and equality saturation, inspired by [egg](https://egraphs-good.github.io/) and [egglog](https://github.com/egraphs-good/egglog). The project is a learning exercise to understand these concepts by implementing them from scratch.

Key components:
- **E-Graph data structures** (`Data.EGraph.*`) - core e-graph representation with e-classes, e-nodes, and union-find
- **E-Matching** (`Data.EGraph.EMatch.*`) - pattern matching including relational e-matching
- **Equality Saturation** (`Data.EGraph.Saturation`) - the main saturation algorithm
- **Linear Haskell data structures** - mutable HashMap (Robin Hood hashing), Set, UnionFind with linear types for safe in-place mutation

The project uses GHC's Linear Haskell extension extensively with `linear-base` and `pure-borrow` for safe, efficient mutable data structures.

## Linear Haskell Best Practices

- If you want to use mutable resources purely, always bind them linearly
- When let-binding linear resources locally, use `let %1 !x = ...` instead of `let x = ...`
- When defining local auxiliary functions that handle linear resources in a `where` clause, always specify the function signature explicitly - GHC cannot infer linearity otherwise. Use `ScopedTypeVariables` extension to bring type parameters into scope.
- `Unsafe.toLinear` is a last resort and SHOULD NOT be used unless you are 100% certain there is no resource leakage in that code

## Haskell Development

- Use `cabal` CLI for Haskell environment interaction (building, testing, running)
- Prefer Haskell LSP tools for codebase information and diagnostics before compiling
- Use `/hoogle` skill to search for external Haskell functions, types, and definitions
- Use `/hackage` skill to read documentation or source code of external packages
