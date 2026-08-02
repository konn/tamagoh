#!/usr/bin/env bash
#
# The command CodSpeed measures. Invoked as `codspeed run -- bash
# ci/scripts/codspeed-bench.sh`, with the two binaries passed in the
# environment.
#
# Scope is the e-graph suite, and within it tamagoh's own leaves:
#
#   tamagoh-bench-hashmap is not measured here at all. It compares tamagoh's
#   Robin Hood table against linear-base and unordered-containers, which is a
#   design question about data structures rather than the thing this project
#   is: it can stay a local `cabal bench`.
#
#   hegg is dropped from the math suite for the same reason in sharper form.
#   It is the rival implementation, not ours -- nothing in this repository can
#   move its numbers, so tracking them spends roughly 45% of the suite's
#   measured work on a series nobody can act on, and turns a bump of the hegg
#   dependency into a "regression" sitting next to tamagoh's own. The
#   tamagoh-vs-hegg comparison the tuning work runs on stays where it belongs:
#   a plain `cabal bench`, which is unfiltered.
#
# `$NF` is the leaf name in tasty's awk-like pattern language, so the filter
# keeps every `.tamagoh` leaf and drops every `.hegg` one without naming a
# single case -- new controlled cases are covered automatically.
#
# It does not skip hegg entirely: annotateControlled still saturates each case
# with hegg once before defaultMain is reached, because the benchmark names
# carry the graph sizes it cross-checks against. That runs outside every
# measurement window, so it costs wall-clock and reports nothing -- and it is
# now most of this command's runtime.
#
# codspeed-hs-rewrite runs last, and inside the measured command on purpose:
# Callgrind writes the profile when the benchmark process exits and the runner
# tars the profile folder when this whole command returns, so between those two
# moments is the only window in which the file exists and is still ours. It
# runs under Valgrind too, which is why it is a single ByteString pass.
set -euo pipefail

: "${MATH_BIN:?set MATH_BIN to the tamagoh-bench-math binary}"
: "${REWRITE_BIN:?set REWRITE_BIN to the codspeed-hs-rewrite binary}"

SIDECAR_DIR="${SIDECAR_DIR:-sidecar}"
mkdir -p "${SIDECAR_DIR}"

CODSPEED_HS_SIDECAR="${SIDECAR_DIR}/allocation-math.csv" \
  "${MATH_BIN}" --pattern '$NF != "hegg"'

# Decodes the z-encoded GHC symbols in the profile the run just wrote, so
# CodSpeed's flamegraph reads `Data.EGraph.Saturation.$wsaturate` rather than
# `tmgh_DataziEGraphziSaturation_zdwsaturate_info`. A pure rename: every cost
# line is copied through, so the reported metric is untouched. Failure is not
# fatal on its side, and must not be fatal here either -- an unrewritten
# profile is worth more than no measurement.
"${REWRITE_BIN}" || echo "::warning::codspeed-hs-rewrite failed; profile uploads with raw symbols"
