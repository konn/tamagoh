# Project Guidelines

## Overview

**tamagoh** is a Haskell implementation of e-graphs and equality saturation, inspired by [egg](https://egraphs-good.github.io/) and [egglog](https://github.com/egraphs-good/egglog). The project is a learning exercise to understand these concepts by implementing them from scratch.

Key components:
- **E-Graph data structures** (`Data.EGraph.*`) - core e-graph representation with e-classes, e-nodes, and union-find
- **E-Matching** (`Data.EGraph.EMatch.*`) - pattern matching including relational e-matching
- **Equality Saturation** (`Data.EGraph.Saturation`) - the main saturation algorithm
- **Linear Haskell data structures** - mutable HashMap (Robin Hood hashing), Set, UnionFind with linear types for safe in-place mutation

The project uses GHC's Linear Haskell extension extensively with `linear-base` and `pure-borrow` (with `linear-witness` and `linear-array-extra`) for safe, efficient mutable data structures.

## Linear Haskell Best Practices

- If you want to use mutable resources purely, always bind them linearly
- When let-binding linear resources locally, use `let %1 !x = ...` instead of `let x = ...`
- When defining local auxiliary functions that handle linear resources in a `where` clause, always specify the function signature explicitly - GHC cannot infer linearity otherwise. Use `ScopedTypeVariables` extension to bring type parameters into scope.
- `Unsafe.toLinear` is a last resort and SHOULD NOT be used unless you are 100% certain there is no resource leakage in that code
- `linear-base` provides only linear boxed arrays/vectors only, and unboxed ones are provided by `linear-array-extra`.

## Performance Tuning Best Practices

Before you do the performance tuning, you must first take the corresponding benchmark suite and use it as a baseline. If no corresponding benchmark suite is found, please start from implementing it before you do performance tuning.

## Haskell Development

- Use `cabal` CLI for Haskell environment interaction (building, testing, running)
- Prefer Haskell LSP tools for codebase information and diagnostics before compiling
- Use `/hoogle` skill to search for external Haskell functions, types, and definitions
  + **Exception**: None of `pure-borrow`, `linear-witness`, and `linear-array-extra` are not published on Hackage yet. For those packages, please consult the corresponding GitHub repository.
- Use `/hackage` skill to read documentation or source code of external packages
  + Same Exception as above applies here.
- DO NOT inspect under `dist-newstyle` unless you are looking for `.ddump-*` file emitted by GHC. The directory is a build cache, and it is quite difficult to gain the sensible information from there.
- GitHub repository for non-hackage packages can be read from @cabal.project

### Testing & Benchmarking

- Test suite and benchmarking suite is defined in `*.cabal` files.
- To run test suite, use `cabal test ...`; for benchmarks `cabal bench ...`.
  + You can use as many `--test-options=".."` (multiple options separated by white spaces) and `--test-option=".."` (as a single option containing whites paces) to pass the test option(s).
  + The same applies to `--benchmark-options` and `--benchmark-option`.
