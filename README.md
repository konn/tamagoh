# tamagoh - Understanding egg/egglog by implementing it

This is my personal project to understand egg (e-graphs good) and egglog by implementing it in Haskell.
For serious usage, go to [hegg][hegg].

[hegg]: https://hackage.haskell.org/package/hegg

## Benchmarking

Two `tasty-bench` suites, both run on every pull request by the
[CodSpeed workflow](.github/workflows/codspeed.yml):

```bash
cabal bench tamagoh-bench-math
```

```bash
cabal bench tamagoh-bench-hashmap
```

They import `Test.Tasty.Bench.CodSpeed` from
[konn/haskell-codspeed][haskell-codspeed] rather than `Test.Tasty.Bench`, which
changes nothing when run this way — same adaptive timing loop, same output,
same `--csv` / `--baseline` / `--svg`. Under `codspeed run` each `bench` leaf
instead becomes its own CodSpeed benchmark, measured in a window opened around
that leaf alone, so the reported number is not dominated by RTS startup and
input construction.

Each run also writes per-benchmark **allocated bytes**, taken from GHC's
per-thread allocation counter:

```bash
CODSPEED_HS_SIDECAR=alloc.csv cabal bench tamagoh-bench-math
```

For fixed code and input that figure is exact and reproducible, which for a
deterministic saturation algorithm makes it the sharper of the two signals —
`codspeed-hs-compare baseline.csv alloc.csv` diffs two runs, and CI does this
against `main`.

`-A32m -T -V0 -I0` in both suites' `with-rtsopts` is part of the measurement
contract, not decoration: changing `-A` shifts instruction counts exactly as a
code change would and invalidates the CodSpeed baseline. `CodSpeed.RTS.Preflight`
reports on stderr when the flags are wrong.

[haskell-codspeed]: https://github.com/konn/haskell-codspeed

## References

- "[egg: Fast and Extensible Equality Saturation](https://arxiv.org/abs/2004.03082)" by Willsey, Nandy, Wang, Flatt, Tatlock, and Panchekha.
- "[Relational E-Matching](https://arxiv.org/abs/2108.02290)" by Zhang, Wang, Wilsey, and Tatlock.
- "[Better Together: Unifying Datalog and Equality Saturation](https://arxiv.org/abs/2304.04332)" by Zhang, Wang, FLatt, Cao, Zucker, Rosenthal, Tatlock, and Wilsey.
- "[hegg: Fast equality saturation in Haskell][hegg]" by Rodrigo Mesquita

## Etymology

"Tamago (卵 or 玉子 in Kanji; たまご in Hiragana)" means "egg" in Japanese.
The suffix "-h" is purely borrowed from *H*askell.
