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

### Guiding Principles (learned from the 2026-07 hegg-parity work; see `workspace/TUNE-PLAN.md`)

1. **Scheduling dominates micro-optimisation.** In equality saturation, *which* rewrites get
   applied matters far more than how fast each one is applied. Keep the backoff scheduler
   hegg/egg-faithful: apply ALL matches of non-banned rules (never truncate a rule's match list —
   truncation makes the applied-rewrite set depend on internal enumeration order), ban by total
   substitution size (#matches × #query-vars), and let bans take effect on later iterations.
2. **Trajectories are cliff-sensitive; keep the engine deterministic and order-robust.** Near
   `nodeLimit`/`maxIterations` cliffs, any change to enumeration order can swing a case ~2×
   either way. Never rely on hash-iteration or heap-internal order for anything semantic; use
   deterministic, name-independent orders (e.g. ascending interned ids). Judge benchmarks by the
   i1–i6 aggregate, not single cases.
3. **The match engine speaks dense `Int`s; user names live only at the boundary.** Pattern
   variables are interned to `0..n-1` (`varNames` maps back); substitutions, positions and
   domains are `IntMap`/`IntSet`; the `Trie` caches a per-level key-set so single-occurrence
   domains are O(1). Nothing in the join's inner loop may hash or compare structured data.
4. **Accumulate in a free monoid, materialise once.** A strict fold (`foldMap'`,
   `IM.fromListWith`, …) over the *list* monoid is a quadratic left-nested `(++)` trap — this bug
   was found three separate times. Use `FMList`/`DList` and convert with `toList` at the boundary.
5. **In pure-borrow hot loops, prefer direct recursion over transformer towers.** Per-element
   `UrT`/`StateT`-over-`BO` traversals and per-element sub-lifetimes (`sharing`/`reborrowing`
   inside a loop body) are measurable constants. Flatten to explicit `BO`-level recursion over
   `F.toList` + a `refill` of the node shape; `share` a borrow once *outside* the loop and
   `upcast` it in; consolidate adjacent reborrow blocks with `.@` record splits.
6. **Separate congruence dirtiness from analysis dirtiness** (egg's `pending` vs
   `analysis_pending`): `repair` restores congruence only; `repairAnal` propagates analysis
   changes, and only for classes whose analysis value actually changed (detected at the meet).
7. **Per-iteration work should be proportional to what changed** — or at least cheap per node.
   No whole-graph snapshots per iteration; fetch class data on demand for the matches that need
   it; the database build must not deep-copy nodes.
8. **Measure before keeping.** Every optimisation lands with a before/after CSV
   (`cabal bench tamagoh-bench-math --benchmark-options "--csv ..."`) and an unchanged test
   outcome; re-profile (`cabal-bench.project`, `-fprof-late`) after each structural change
   because the ranking shifts. Mutation is not automatically faster: the egg-style register
   vector lost to a ≤7-entry persistent `IntMap` and was rejected. Linear mutation earns its
   place where mutation is real (union-find, hashcons, worklists), not in tiny transient
   accumulators. Beware machine-load drift: hegg runs in the same suite as a control — read
   results *relative* to it.

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

### Debugging

- When you do printf-debugging with `Debug.Trace.trace`, output is printed when the thunk is evaluated, and this needs careful calling of `Debug.Trace.trace`. Here are rule of
  thumbs:
  1. When you are in do-expression, insert `!() <- trace "<error message>" (pure ())
  + when you are under `Control.do`, use `Control.pure ()` instead of unprefixed `pure`
  + when you are under `DataFlow.do`, use plain `()` without `pure`.
  1. When the logging should occur right before/after or in-between let-binds, use `let !() = trace <message> ()`
  2. If you really need to wrap non-unit value with `trace` and it is a linearly bound, use variants from `Debug.Trace.Linear`.
