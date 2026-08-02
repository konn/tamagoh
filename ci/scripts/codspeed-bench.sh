#!/usr/bin/env bash
#
# The command CodSpeed measures. Invoked as `codspeed run -- bash
# ci/scripts/codspeed-bench.sh`, with the three binaries passed in the
# environment.
#
# Both suites run inside ONE `codspeed run`, deliberately. The runner keys an
# upload by run part, and a commit carrying more than one upload is not
# readable: the backend keeps whichever arrived last, and sometimes merges
# them. So there is exactly one measured command per commit, and everything
# that needs measuring goes in it.
#
# Each binary reports under its own component -- Test.Tasty.Bench.CodSpeed
# takes the component from $CODSPEED_HS_COMPONENT, else the program name -- so
# `tamagoh-bench-math:All.controlled...` and `tamagoh-bench-hashmap:All...`
# URIs cannot collide. The sidecar is a single file path, though, so each suite
# is given its own.
#
# codspeed-hs-rewrite runs last, and inside the measured command on purpose:
# Callgrind writes a profile when a benchmark process exits and the runner tars
# the profile folder when this whole command returns, so between those two
# moments is the only window in which the files exist and are still ours. It
# runs under Valgrind too, which is why it is a single ByteString pass.
set -euo pipefail

: "${MATH_BIN:?set MATH_BIN to the tamagoh-bench-math binary}"
: "${HASHMAP_BIN:?set HASHMAP_BIN to the tamagoh-bench-hashmap binary}"
: "${REWRITE_BIN:?set REWRITE_BIN to the codspeed-hs-rewrite binary}"

SIDECAR_DIR="${SIDECAR_DIR:-sidecar}"
mkdir -p "${SIDECAR_DIR}"

CODSPEED_HS_SIDECAR="${SIDECAR_DIR}/allocation-math.csv" "${MATH_BIN}"
CODSPEED_HS_SIDECAR="${SIDECAR_DIR}/allocation-hashmap.csv" "${HASHMAP_BIN}"

# Decodes the z-encoded GHC symbols in the profiles both runs just wrote, so
# CodSpeed's flamegraph reads `Data.EGraph.Saturation.$wsaturate` rather than
# `tmgh_DataziEGraphziSaturation_zdwsaturate_info`. A pure rename: every cost
# line is copied through, so the reported metric is untouched. Failure is not
# fatal on its side, and must not be fatal here either -- an unrewritten
# profile is worth more than no measurement.
"${REWRITE_BIN}" || echo "::warning::codspeed-hs-rewrite failed; profiles upload with raw symbols"
